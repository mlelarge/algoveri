# Tier-1 MCP tools — implementation plan

Three tools, one Python MCP server, ~1 week of work. The plan below
specifies the data sources (probed against Frama-C 32 on this host),
the API of each tool, the parsing rules, the server architecture, and
the test plan.

## 0. Probed Frama-C capabilities (the foundation)

These were verified by running `frama-c -wp` on `algoveri_data/gcd`:

| Need | Frama-C flag / output |
|---|---|
| Per-goal structured output | `-wp-report-json <file>` — emits a JSON array, one entry per goal, with `goal`, `property`, `file`, `line`, `function`, `verdict`, `provers[]`, `passed`, `smoke` |
| Pretty-printed VC (hypotheses + conclusion) | `-wp-print` — emits "Goal <desc> (file X, line Y) in 'fn':\n  Assume { ... }\n  Prove: <expr>." per goal |
| Counter-example | `-wp-counter-examples` — passes the flag through to the prover (Alt-Ergo / Z3); model returned in the prover's output |
| SMT-LIB / Why3 task per goal | `-wp-out <dir>` — writes `<dir>/typed/<goalname>_Why3_<prover>_<version>.why` |
| Target a property by name | `-wp-prop=<name>` — works only if the user **named** the property (`requires Pos: x>0`); does NOT accept generated goal IDs like `compute_gcd_assigns` |
| Target a function | `-wp-fct=<name>` — works |
| Target a property kind | `-wp-prop=@ensures` / `@assigns` / `@assert` / `@requires` — works |

**Key constraint surfaced:** Frama-C does not support per-goal rerun by
generated ID. The agent can target a function or a category, but to
re-check exactly one numbered goal we must run all goals of that
function/category and filter post-hoc. This shapes Tool #2 and Tool
#3's implementation.

**Goal-name format** (decoded from the JSON output):

- `typed_<fn>_ensures` (post-conditions, possibly `_part<N>` suffix)
- `typed_<fn>_assigns` (frame, possibly `_normal_partN`)
- `typed_<fn>_loop_invariant_<N>_<established|preserved>` (loop invariants by occurrence index)
- `typed_<fn>_loop_assigns_<N>`
- `typed_<fn>_loop_variant_<N>_(decrease|positive)`
- `typed_<fn>_assert_<N>` (inline assertions)
- `typed_<fn>_assert_missing_return` (kernel-generated falls-through)
- `typed_<fn>_terminates_part<N>`
- `typed_<fn>_call_<callee>_<requires|assigns>_<N>`

The numeric suffix (`_3_preserved`, `_part04`) is positional — it
**renumbers** when annotations are added or removed. This is the
reason most subagents in this run reported "I can't track which goal
flipped between edits".

## 1. Architecture

```
mcp-server-framac/
├── pyproject.toml
├── README.md
├── src/mcp_framac/
│   ├── __init__.py
│   ├── __main__.py        # python -m mcp_framac → starts server on stdio
│   ├── server.py          # MCP tool registrations (verify, explain_goal, diff_goals)
│   ├── runner.py          # frama-c subprocess wrapper
│   ├── parse_json.py      # parses -wp-report-json output
│   ├── parse_print.py     # parses -wp-print output into Goal/Assume/Prove blocks
│   ├── parse_why3.py      # reads a .why file from -wp-out for SMT-level dumps
│   ├── source_extract.py  # given file+line+kind, extract the surrounding ACSL clause
│   ├── identity.py        # stable goal identity = (function, kind, line, content_hash)
│   ├── cache.py           # per-file LRU of last verify run, in-memory
│   ├── models.py          # pydantic models for tool I/O
│   └── config.py          # FRAMAC env var, defaults, timeouts
└── tests/
    ├── fixtures/
    │   ├── gcd_empty.c        # algoveri_data/gcd/acsl_spec.c snapshot (4/5)
    │   ├── gcd_filled.c       # algoveri_solution/gcd/acsl_spec.c snapshot (9/9)
    │   └── bst_insert_partial.c
    ├── test_parse_json.py
    ├── test_parse_print.py
    ├── test_source_extract.py
    ├── test_identity.py
    ├── test_diff.py
    └── test_integration.py    # actually invokes frama-c, gated by env var
```

**Transport**: stdio (the default for MCP servers). Spawned per-session
by the host (Claude Code / Claude Desktop / Claude API).

**State**: in-memory cache only. Keyed by `(absolute_file_path,
mtime_ns)`. TTL-irrelevant — invalidated on mtime change. Capped at
~50 entries (bench-sized).

**Concurrency**: Frama-C invocations are blocking subprocesses; each
gets its own `tempfile.mkdtemp()` for `-wp-out`, so two concurrent
calls (different files) don't collide. Use `asyncio.to_thread` to
keep the MCP loop responsive.

**Configuration** (env vars, all optional):

| Var | Default | Purpose |
|---|---|---|
| `FRAMAC` | `frama-c` (PATH lookup) | Binary path |
| `FRAMAC_PROVERS` | `alt-ergo,z3` | Comma-separated prover list |
| `FRAMAC_TIMEOUT` | `10` | Per-prover timeout (seconds) |
| `FRAMAC_PAR` | `4` | `-wp-par` value |
| `FRAMAC_TEMPDIR` | system tmp | Where `wp_session` dirs go |

Why config and not tool args? Because on shared hosts the prover
selection is environment-specific (cvc5 not always installed), but the
agent shouldn't have to discover that.

## 2. Tool 1 — `framac.verify`

### 2.1 API

```python
@mcp.tool()
async def verify(
    file_path: str,
    timeout: int | None = None,         # per-prover timeout, defaults FRAMAC_TIMEOUT
    provers: list[str] | None = None,   # defaults FRAMAC_PROVERS
    function: str | None = None,        # restrict to one function (-wp-fct)
    only_kinds: list[str] | None = None # ["ensures","assert","loop_invariant",...]
) -> VerifyResult: ...
```

```python
class Goal(BaseModel):
    id: str               # raw frama-c goal name, NOT stable across edits
    stable_id: str        # (function, kind, line, content_hash) tuple as SHA1[:12]
    kind: str             # "ensures" | "assigns" | "loop_invariant_established" | ...
    function: str
    file: str
    line: int
    clause_text: str | None        # the ACSL annotation source, extracted from the file
    verdict: str          # "valid" | "timeout" | "stepout" | "unknown" | "invalid"
    proved: bool
    provers: list[ProverAttempt]  # [{prover, time_ms, success}]

class VerifyResult(BaseModel):
    proved: int
    total: int
    goals: list[Goal]
    warnings: list[str]   # e.g. "Allocation, initialization and danglingness not yet implemented"
    elapsed_ms: int
    error: str | None     # set on parse failure / non-zero exit; goals list will be empty
```

### 2.2 Implementation steps

1. **Resolve inputs**: absolute path, defaults from config, build the
   command:
   ```
   frama-c -wp
       -wp-timeout {timeout}
       -wp-prover {','.join(provers)}
       -wp-par {par}
       -wp-report-json {tmp}/report.json
       -wp-out {tmp}/wp_session
       [-wp-fct {function}]
       [-wp-prop @{kind} for kind in only_kinds]
       {file_path}
   ```
2. **Spawn**: `asyncio.create_subprocess_exec`, capture stdout/stderr,
   60 s wall-clock hard cap (configurable via `total_timeout`).
3. **Parse the JSON report** (`parse_json.py`). Each entry already has
   `file`, `line`, `function`, `verdict`, `provers`. Map the raw
   `goal` string to `kind` via regex on the suffix:
   ```
   GOAL_KIND_RE = re.compile(
       r"_(?P<kind>ensures|assigns|requires|assert|terminates|"
       r"loop_invariant_\d+_(?:established|preserved)|"
       r"loop_assigns_\d+|loop_variant_\d+_(?:decrease|positive)|"
       r"call_\w+_(?:requires|assigns)_\d+|"
       r"assert_missing_return|assert_\d+)"
       r"(?:_normal)?(?:_part\d+)?$"
   )
   ```
4. **Enrich with `clause_text`** (`source_extract.py`). For a goal at
   `(file, line, kind)`:
   - Open the file, find the nearest preceding `/*@ ... */` block (or
     `//@ ...` line) above `line`.
   - Slice the lines that mention the matching kind. For
     `loop_invariant_3_preserved` we count the 3rd `loop invariant`
     in the enclosing loop's annotation block.
   - Return the textual clause.
5. **Compute `stable_id`** (`identity.py`): `sha1(f"{function}|{kind}|{line}|{clause_text}")[:12]`.
   For loop invariants on the same line, the content_hash disambiguates.
6. **Parse warnings** from stderr (`Allocation, initialization and
   danglingness…`, `Missing RTE guards`, etc.) — passed through.
7. **Cache** `(file_path, mtime) → VerifyResult` for `diff_goals` to
   look up.
8. **Cleanup**: `tmp` dir is removed on success; kept on `error` and
   path returned in the error message for debugging.

### 2.3 Example output (gcd, empty body)

```json
{
  "proved": 4,
  "total": 5,
  "elapsed_ms": 850,
  "warnings": ["Body of function compute_gcd falls-through. Adding a return statement"],
  "goals": [
    {
      "id": "typed_compute_gcd_ensures",
      "stable_id": "8a7b3c1d4e21",
      "kind": "ensures",
      "function": "compute_gcd",
      "file": "/tmp/.../acsl_spec.c",
      "line": 19,
      "clause_text": "ensures \\result == spec_gcd(a, b);",
      "verdict": "valid", "proved": true,
      "provers": [{"prover":"qed","time_ms":0,"success":true}]
    },
    {
      "id": "typed_compute_gcd_assert_missing_return",
      "stable_id": "1f2e3d4c5b6a",
      "kind": "assert_missing_return",
      "function": "compute_gcd",
      "file": "/tmp/.../acsl_spec.c",
      "line": 23,
      "clause_text": "// Implement and verify compute_gcd here.",
      "verdict": "timeout", "proved": false,
      "provers": [
        {"prover":"qed","time_ms":1,"success":false},
        {"prover":"Alt-Ergo:2.6.2","time_ms":0,"success":false}
      ]
    }
  ]
}
```

### 2.4 Effort

~1 day. Most of the work is `source_extract.py` for the
loop-invariant disambiguation; the rest is glue.

## 3. Tool 2 — `framac.explain_goal`

### 3.1 API

```python
@mcp.tool()
async def explain_goal(
    file_path: str,
    goal: str,                       # accepts either raw `id` or `stable_id`
    timeout: int | None = None,
    with_counterexample: bool = False,
    with_smt_dump: bool = False
) -> ExplainResult: ...
```

```python
class Hypothesis(BaseModel):
    section: str         # "Type" | "Heap" | "Pre" | "Invariant" | "Have" | "When" | "Goal"
    text: str

class ExplainResult(BaseModel):
    goal_id: str
    stable_id: str
    kind: str
    function: str
    source_loc: SourceLoc       # {file, line, clause_text}
    hypotheses: list[Hypothesis]
    conclusion: str             # the body of `Prove: ...`
    prover_attempts: list[ProverAttempt]
    counterexample: dict | None # parsed model from prover, if requested
    smt_dump: str | None        # contents of <wp_out>/typed/<goalname>_Why3_*.why
    suggestions: list[str]      # heuristic hints: "Hypothesis missing \\separated(p, q)", etc.
```

### 3.2 Implementation steps

1. **Resolve goal**: look up the `stable_id` in the cache (`verify`'s
   last run on this file). Fail fast with a clear error if no recent
   verify result is cached.
2. **Re-run frama-c with `-wp-print`** restricted to the goal's
   function: `-wp-fct={function}`. We can't slice further with
   `-wp-prop=` for a generated goal name, but `-wp-fct` plus
   post-hoc filtering is fast enough.
   - Optionally add `-wp-counter-examples` and `-wp-prover alt-ergo` if
     `with_counterexample=true` (Alt-Ergo's model output is the most
     parseable).
3. **Parse `-wp-print` output** (`parse_print.py`). The format is:
   ```
   Goal <description> (file X, line Y) in '<fn>':
   Assume {
     Type: ...
     (* Heap *)
     Type: ...
     (* Pre-condition *)
     Have: ...
     (* Invariant *)
     Have: ...
   }
   When: ...     # optional, for hypotheses introduced at the goal point
   Prove: <expr>.
   Prover <prover> returns <Valid|Timeout|Unknown> (Xms)
   ```
   A simple state machine (or `pyparsing` if you prefer) reads from
   `Goal ` to the next `Goal ` or terminator and emits structured
   hypotheses. Section dividers like `(* Pre-condition *)` annotate the
   following `Type:`/`Have:` line.
4. **Match the goal**: each `Goal <description> (file X, line Y)` maps
   back to a JSON entry by `(file, line, kind)`. We pick the one
   whose `stable_id` matches the input.
5. **Counterexample parsing** (optional). Alt-Ergo prints models in a
   recognizable format if `-wp-counter-examples` is set; parse on a
   best-effort basis. Z3's model is more uniform but Alt-Ergo gives
   more readable variable names. Implement both, return whichever
   comes first.
6. **SMT dump** (optional): read the `.why` file from `<tmp>/wp_session/typed/<goalname>_Why3_<prover>.why`.
7. **Heuristic suggestions** (small ruleset, valuable for the agent):
   - `\fresh(...)` mentioned in conclusion AND warning "Allocation
     not yet implemented" present → suggest "WP's allocation model is
     incomplete; `\fresh` hypotheses are dropped. Try a non-allocating
     implementation or accept this as a structural ceiling."
   - Two pointer parameters in Pre, conclusion involves an aliased
     write → suggest "Add `\separated(p, q)` to the contract (or
     verify under `-wp-model Typed+ref`)."
   - Conclusion is `\forall ...` and one prover returned `Unknown`
     (not `Timeout`) → suggest "Goal may be vacuously true or
     genuinely false; the prover gave up rather than timed out."
   - Conclusion involves `(a*b)%p` patterns → suggest "Modular
     arithmetic; consider Russian-peasant decomposition."
   The list grows organically; start with these four — they map to the
   most common friction-journal entries in this run.

### 3.3 Effort

~2 days. The `-wp-print` parser is the bulk; the heuristics are
small once the structure is in place.

## 4. Tool 3 — `framac.diff_goals`

### 4.1 API

```python
@mcp.tool()
async def diff_goals(
    file_path: str,           # the "after" file
    baseline: str | None = None  # path to the "before" file; or None to use cached prior verify of file_path
) -> DiffResult: ...
```

```python
class GoalRef(BaseModel):
    stable_id: str
    kind: str
    function: str
    line: int
    clause_text: str | None
    verdict: str

class DiffResult(BaseModel):
    newly_proved: list[GoalRef]      # in after, valid; was invalid (or absent) in before
    newly_failed: list[GoalRef]      # in after, invalid; was valid in before
    still_proved: list[GoalRef]
    still_failed: list[GoalRef]
    added: list[GoalRef]              # in after only (e.g., new assertion the user wrote)
    removed: list[GoalRef]            # in before only (e.g., removed assertion)
    summary: dict                     # {before:{proved,total}, after:{proved,total}, delta_proved}
```

### 4.2 Implementation steps

1. **Get `before_goals`**: if `baseline` is given, run `verify` on it.
   Otherwise look up the cache for `file_path` from the most recent
   `verify` call (the typical workflow is `verify; edit; diff_goals`).
2. **Get `after_goals`**: run `verify` on `file_path`.
3. **Match**: build dicts keyed by `stable_id`. The two interesting
   cases:
   - Same content_hash → same goal, status compared directly.
   - Different content_hash but same `(function, kind, line)` → user
     edited the annotation in place; reported as `removed + added`
     rather than `unchanged` (so the user can see the change).
4. **Set-diff** by stable_id, classify each goal.
5. **Summarize**: `delta_proved = after.proved - before.proved`. If
   negative, the edit hurt; if positive, it helped.
6. **Output ordering**: `newly_failed` first (regressions), then
   `newly_proved`, then everything else. Helps the agent triage.

### 4.3 Edge cases

- **The "added" stable_id is a fresh goal whose clause_text is identical
  to a removed one** — i.e., the user moved an assertion to a different
  line. With `(function, kind, line, content_hash)` identity, this
  shows up as `removed + added`. Acceptable; the agent sees both
  events. Could be smarter (line-fuzzy matching) but added complexity
  for marginal value.
- **Loop renumbering**: adding a `loop invariant` between two existing
  ones changes the positional `_2`, `_3`, `_4`. Their `stable_id`s
  (content_hash-based) survive intact, but the raw `id` field
  changes. Document this clearly in the tool's description.
- **No baseline cached**: the caller must run `verify` first or
  provide an explicit `baseline=`. Return a clear error rather than
  silently re-verifying.

### 4.4 Effort

~1 day. Trivial once `verify` exists.

## 5. Server skeleton (~150 LOC)

```python
# src/mcp_framac/server.py
from mcp.server.fastmcp import FastMCP
from mcp_framac.runner import run_wp
from mcp_framac.parse_json import parse_report
from mcp_framac.source_extract import enrich_with_clause_text
from mcp_framac.cache import VerifyCache
from mcp_framac.models import VerifyResult, ExplainResult, DiffResult

mcp = FastMCP("framac")
cache = VerifyCache(maxsize=50)

@mcp.tool()
async def verify(file_path, timeout=None, provers=None,
                 function=None, only_kinds=None) -> VerifyResult:
    cmd = build_wp_command(file_path, timeout, provers, function, only_kinds)
    proc = await run_wp(cmd)
    if proc.returncode not in (0, 1):  # 0 = all proved, 1 = some unproved
        return VerifyResult(error=proc.stderr.decode()[-2000:],
                            proved=0, total=0, goals=[],
                            warnings=[], elapsed_ms=proc.elapsed_ms)
    goals_json = parse_report(proc.report_json_path)
    goals = enrich_with_clause_text(goals_json, file_path)
    result = VerifyResult(
        proved=sum(1 for g in goals if g.proved),
        total=len(goals),
        goals=goals,
        warnings=extract_warnings(proc.stderr),
        elapsed_ms=proc.elapsed_ms,
    )
    cache.put(file_path, result)
    return result

@mcp.tool()
async def explain_goal(...): ...

@mcp.tool()
async def diff_goals(...): ...

if __name__ == "__main__":
    mcp.run()
```

## 6. Test plan

### 6.1 Fixture corpus

Pull from this run's `algoveri_solution/`:

| Fixture | Expected | Purpose |
|---|---|---|
| `gcd_empty.c` (algoveri_data) | 4/5, one timeout | Baseline partial |
| `gcd_filled.c` (algoveri_solution after pilot) | 9/9 | Baseline all-proved |
| `bst_insert_partial.c` (algoveri_solution) | 20/37 | Multi-failure, multiple kinds |
| `dijkstra_partial.c` | 17/18 | Single-stuck-ensures pattern |
| `bubble_sort_filled.c` | 61/61 | Many goals, ghost loops |

### 6.2 Unit tests

- `test_parse_json`: hand-crafted JSON snippets for valid / timeout /
  stepout / multi-prover; assert correct mapping.
- `test_parse_print`: a captured `-wp-print` output for `bst_insert`,
  asserts that we extract Hypothesis sections, conclusion, prover
  attempts.
- `test_source_extract`: each fixture's known goal+line maps to the
  expected ACSL clause text (use the `clause_text` field from the
  pilot JSONs as ground truth).
- `test_identity`: assert `stable_id` is invariant under reordering of
  goals in the JSON, and changes when the clause text is edited.
- `test_diff`: `gcd_empty → gcd_filled` produces 5 newly_proved, 0
  newly_failed; `bubble_sort_filled → bubble_sort_with_typo` produces
  1 newly_failed.

### 6.3 Integration tests (gated by env var, real frama-c)

- `verify(gcd_empty.c)` → 4/5, the assert_missing_return goal is
  reported with `verdict=timeout`.
- `explain_goal(gcd_empty.c, <timeout-goal-stable-id>)` → returns the
  Goal block, hypotheses, the conclusion (which is the postcondition
  body), and the prover attempts.
- `diff_goals(gcd_empty.c, gcd_filled.c)` → exactly 5 newly_proved.
- Concurrency: two simultaneous `verify(...)` calls on different
  files don't race.

### 6.4 Cross-check against this run's results

For each of the 21 all-proved problems, `verify` should return `proved
== total`. For each of the 56 partial, `verify` should return the same
proved/total counts as recorded in `results/acsl_session/<name>.json`.
Run as a one-shot regression suite.

## 7. Packaging & install

```toml
# pyproject.toml
[project]
name = "mcp-server-framac"
version = "0.1.0"
dependencies = [
    "mcp>=1.0",
    "pydantic>=2",
]

[project.scripts]
mcp-server-framac = "mcp_framac.__main__:main"
```

### Claude Code install (per-project, in `.mcp.json`)

```json
{
  "mcpServers": {
    "framac": {
      "command": "python",
      "args": ["-m", "mcp_framac"],
      "env": {
        "FRAMAC": "/opt/opam/acsl/bin/frama-c",
        "FRAMAC_PROVERS": "alt-ergo,z3",
        "FRAMAC_TIMEOUT": "10"
      }
    }
  }
}
```

The agent invokes the tools as `mcp__framac__verify(...)`,
`mcp__framac__explain_goal(...)`, `mcp__framac__diff_goals(...)`.

### Claude Desktop install

Same config block, in `~/Library/Application Support/Claude/claude_desktop_config.json` (macOS) or the equivalent on Linux/Windows.

## 8. Risks / open questions

1. **Goal-id stability is a footgun.** The raw `id` field is
   positional and changes when annotations are added. The
   `stable_id` (content-hash-based) survives, but the agent must use
   it consistently. Document this prominently in each tool's docstring
   so the LLM picks it up via the MCP tool description.
2. **`-wp-print` output volume** on big files is large (~30 KB). For
   `explain_goal`, we run with `-wp-fct=<one_function>` to slice
   down, but if the function is itself huge (`bubble_sort` is 80
   lines + 7 ghost loops) the dump can still be 8-10 KB. Acceptable
   but the tool description should note that callers should only
   invoke `explain_goal` on a specific goal, not fish through everything.
3. **Counter-example mode is fragile.** Alt-Ergo's model output
   format is undocumented and varies by version. Implement parsing
   on a best-effort basis; if parse fails, return the raw model
   string under `counterexample.raw`. Don't promise structured output.
4. **Frama-C version drift.** This plan is grounded in Frama-C 32
   (Germanium). The JSON schema is stable since Frama-C ~24, but the
   `goal` name format has changed across versions. Add a
   `frama-c -version` check in `runner.py` and warn loudly on
   unsupported versions.
5. **Why3 session reuse.** Frama-C can persist a Why3 session for
   incremental verification (`-wp-out` + `-wp-cache update`). A future
   tool (`framac.verify_incremental`) could exploit this to make the
   "goal-level rerun" of agent dreams real — re-checking only goals
   whose hypotheses changed. Out of scope for Tier-1; it's the
   obvious Tier-2 follow-up.
6. **Tool argument validation.** `file_path` must be inside a
   user-controlled directory. Don't blindly `frama-c` arbitrary
   paths; reject path traversal attempts. Easy with `pathlib`.

## 9. Effort summary

| Item | Estimate |
|---|---:|
| Tool 1 (`verify`) | 1 day |
| Tool 2 (`explain_goal`) | 2 days |
| Tool 3 (`diff_goals`) | 1 day |
| Tests + fixtures | 1.5 days |
| Packaging + install docs | 0.5 day |
| **Total** | **~6 days** solo |

After build: a follow-up benchmark pass with the three tools enabled,
same protocol, would let us measure the actual uplift against this
run's 27.3 % baseline. Predicted **45 %** based on §7 of
`results/acsl_session/summary.md`.

## 10. Out of scope (explicitly Tier-2 or later)

- Goal-level incremental rerun (needs Why3 session caching)
- Per-prover fallback / portfolio mode (`mcp__framac__try_provers`)
- ACSL syntax linter / cheatsheet (separate `mcp__acsl__lint` server)
- Snippet library (separate corpus indexer)
- Anti-cheat diff against a frozen baseline (separate `mcp__acsl__diff_check`)
- Ghost-witness scaffolding helpers
- Memory-model picker (`mcp__framac__try_models`)

These all matter and showed up in the friction journals, but each is
its own small server and shouldn't block Tier-1.
