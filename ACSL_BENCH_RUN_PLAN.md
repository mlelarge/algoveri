# ACSL benchmark — Claude Code agent loop, MCP-tool discovery

The point of this experiment is **not** to publish a score against
AlgoVeri's table. It's to run Claude Code agents on the 77
`algoveri_data/<name>/acsl_spec.c` problems, observe where the agent loop
struggles, and use those traces to design **MCP tools** that would lift
performance on a follow-up run.

Two outputs:

1. A baseline pass-rate (`X / 77`) with **no MCP tools**, just the stock
   Claude Code surface (Read, Edit, Write, Bash).
2. A **list of proposed MCP tools**, each tied to specific failure
   modes observed in the agent transcripts.

A second pass with the most promising tools enabled would close the
loop, but is out of scope for this run.

---

## 1. Verifier — native, no container

Frama-C 32 + Alt-Ergo 2.6.2 + Z3 + Why3 1.8.2 are already installed at
`/opt/opam/acsl/bin/`. Confirmed working on `gcd` (`Proved goals: 4 / 5`
with the empty body — postcondition unprovable, as expected).

Per-problem invocation (the agent runs this itself):

```bash
frama-c -wp -wp-timeout 10 -wp-prover alt-ergo,z3 -wp-par 4 <file>
```

Pass criterion: line `[wp] Proved goals:    N / N` with `N > 0` and
both numbers equal. (For partial credit during analysis: record both
numbers.)

No Apptainer. No `acsl_verifier.py`. No edits to `src/`. Just Bash.

## 1b. Workspace — `algoveri_solution/`, source untouched

The 77 `acsl_spec.c` files have been copied into a parallel
`algoveri_solution/<name>/acsl_spec.c` tree. Subagents work on the
copies; `algoveri_data/` is the read-only source-of-truth and the
baseline for the anti-cheat diff (§2.3). Natural-language descriptions
(`verus_nl.txt`) are read in place from `algoveri_data/<name>/` — they
are never written to.

To reset the workspace at any point:
```bash
rm -rf algoveri_solution
mkdir -p algoveri_solution
for d in algoveri_data/*/; do
    name=$(basename "$d")
    [ -f "$d/acsl_spec.c" ] || continue
    mkdir -p "algoveri_solution/$name"
    cp "$d/acsl_spec.c" "algoveri_solution/$name/acsl_spec.c"
done
```

Idempotent and cheap.

## 2. Mechanics — main agent dispatches, subagents solve

### 2.1 Roles

- **Main agent** (this session): orchestrator. Picks the next problem
  to run, spawns a subagent, collects its report, writes results.
- **Per-problem subagent** (`Agent` tool, `subagent_type:
  "general-purpose"`): does the actual work on one
  `algoveri_solution/<name>/acsl_spec.c`. Has Read / Edit / Write /
  Bash. Reports back a structured JSON.

No worktree isolation needed: each subagent owns a unique file path
(`algoveri_solution/<name>/acsl_spec.c`), and a batch only contains
distinct problems, so parallel subagents never touch the same file.
Reset semantics in §1b cover the "subagent corrupted the workspace"
case.

### 2.2 Subagent prompt (copy verbatim into the `Agent` call)

```
You are scoring Claude Code on the AlgoVeri ACSL benchmark.

Problem: <name>
File:    <repo>/algoveri_solution/<name>/acsl_spec.c
NL:      <repo>/algoveri_data/<name>/verus_nl.txt   (read-only context)
Original (for your own reference; never edit, never copy back):
         <repo>/algoveri_data/<name>/acsl_spec.c

Task: replace the empty function body (the line
`// Implement and verify <name> here.`) with a complete C
implementation plus whatever ACSL annotations are needed, so that
Frama-C's WP plugin discharges every proof obligation.

Hard rules (will be diff-checked at the end):
- Do NOT modify the function contract (the `/*@ … */` immediately
  above the function).
- Do NOT modify the preamble (predicate / logic / axiomatic blocks).
- Do NOT modify any typedef.
- Do NOT use ACSL `assumes` (note: `assigns` is fine), do NOT add
  `lemma … : \true` or `\false`, do NOT weaken existing predicates.
- You MAY add inside the body: `//@ loop invariant`, `loop variant`,
  `loop assigns`, `//@ assert ...`, ghost variables.

Verifier:
  frama-c -wp -wp-timeout 10 -wp-prover alt-ergo,z3 -wp-par 4 <file>

Pass: stdout contains a line matching
  [wp] Proved goals:    N / N
with N > 0 and both numbers equal.

Iterate as needed. Stop when proved, or when you've spent 60 frama-c
runs without progress, or after 20 minutes wall-clock — whichever
first.

—————————————————————————————————————————————————————————————
META-OBSERVABILITY (this is the actual point of the run):

Throughout your work, keep a running journal of friction points. Add
an entry every time you hit one of:
  - syntax / semantics confusion about an ACSL construct,
  - WP output you couldn't quickly parse for the actionable info,
  - a feedback loop that felt too slow (re-running the whole file
    when you only wanted one goal, etc.),
  - a fact you wished you had a tool for (an ACSL reference, a
    library of working invariants, a diff against the original spec,
    Why3 session inspection, …).

Each journal entry: 1–2 sentences, the verbatim friction. Don't
philosophize, just log.

Report back ONLY this JSON, nothing else:
{
  "name": "<problem name>",
  "verdict": "all_proved" | "partial" | "failed" | "gave_up",
  "proved": <int>, "total": <int>,
  "frama_c_runs": <int>,
  "wall_clock_seconds": <int>,
  "final_file_path": "<absolute path inside your worktree>",
  "summary": "<2-4 sentences>",
  "friction_journal": [ "<entry 1>", "<entry 2>", ... ],
  "tool_wishlist": [ "<concrete MCP tool I wished existed>" ]
}
```

The `friction_journal` and `tool_wishlist` fields are the experiment's
primary instrument. The `verdict` is secondary.

### 2.3 Anti-cheat — diff at end of run

`algoveri_data/<name>/acsl_spec.c` is the frozen baseline. After each
subagent reports back, the main agent runs:

```bash
diff algoveri_data/<name>/acsl_spec.c algoveri_solution/<name>/acsl_spec.c
```

and rejects (= scores as `failed_cheat`) any diff that touches lines
*outside* the function body, or that introduces `assumes`,
`lemma … : \true`, or new `axiomatic` blocks. Mechanical, no LLM in the
loop.

## 3. Concurrency, scheduling, and budget

- **Concurrency**: 4 subagents in parallel. Frama-C uses `-wp-par 4`
  per invocation, so 4 × 4 = 16 cores nominal. Bump to 8 if the box
  has the cores and Alt-Ergo doesn't thrash.
- **Per-problem cap**: 60 frama-c runs OR 20 min wall-clock per
  subagent (enforced inside the subagent prompt; the orchestrator
  trusts the cap because subagents are well-behaved on it).
- **Global cap**: 5 hours wall-clock for the full 77. Whatever's
  unfinished gets scored as `unrun` and noted in the summary.
- **Scheduling**: dispatch in 4-wide batches. The main agent sends a
  single message containing 4 parallel `Agent` calls, waits for all
  four results, then dispatches the next batch. 77 problems / 4 ≈ 20
  batches. (`Agent` calls support `run_in_background: true` if a
  later refinement wants overlapping batches; for the first run, keep
  it synchronous so the orchestration is dead simple.)

## 4. Vacuity probe — keep, run before the bench

Same as previous plan revisions. `ACSL_REALIGNMENT.md` §3.4 flags
unverified contract vacuity; a `requires \false` would silently pass.

Before scoring: for each spec, write a deliberately wrong stub body
and confirm WP fails. This is mechanical and not a subagent task —
the main agent does it directly with Bash + Edit. Files where a wrong
body still proves are flagged and either patched or excluded.

## 5. Aggregation

Per-problem JSON → `results/acsl_session/<name>.json`.

Aggregate `results/acsl_session/summary.md` with:

- **Headline**: `X / 77 = X.X %` baseline pass-rate, no MCP tools.
- **Per-category**: same six buckets as
  `scripts/runs_example_scripts/run_task_gemini.sh`.
- **Failure-mode histogram**: bin every `friction_journal` entry into
  ~6–10 categories (manual pass; this is *the* analysis step). Each
  category gets a count and 2–3 verbatim examples.
- **Tool wishlist (deduped)**: union of all subagents'
  `tool_wishlist` arrays, deduped, ranked by how many subagents
  independently asked for the same thing.
- **Proposed MCP tools** (synthesis from the previous two): each one
  named, with (a) which failure-mode bucket it addresses, (b) a
  one-paragraph sketch of the tool's API, (c) a guess at the
  pass-rate uplift if it had been available.

## 6. Hypothesis — MCP tools we expect to want

Useful to write *before* the run so we can falsify or confirm:

1. **`framac.verify(file) → {proved, total, unproved: [{name, loc,
   prover, hint}]}`** — replaces the agent's `bash + grep [wp]`
   ritual. Cuts every revision iteration's token cost roughly in half
   (WP raw output is verbose).
2. **`framac.unproved_only(file) → [goal]`** — focused, structured,
   per-goal. Lets the agent target one failing obligation at a time
   instead of replaying the whole file.
3. **`acsl.docs(symbol)`** — built-in docs for `\valid`, `\valid_read`,
   `\separated`, `\at(e, L)`, multi-label functions, `assigns`
   syntax, `reads` clauses on `logic` functions. Replaces "guess + WP
   error" loops on syntax.
4. **`acsl.snippets(query)`** — tiny library of working invariant
   patterns: "loop invariant for sortedness up to i", "frame condition
   for path compression", "loop variant for binary search",
   "permutation via multiset count". Empirically, models converge
   faster with examples than with axiomatic descriptions.
5. **`why3.session(file) → {goals, applied_tactics, remaining}`** —
   inspection of the WP-generated Why3 session, so the agent can see
   *which* sub-goal of `ensures` failed rather than just "ensures
   line N failed".
6. **`framac.replay(file, prover, timeout)`** — re-run a single goal
   with a different prover (`cvc4`, `cvc5`) or longer timeout, without
   the agent re-typing the whole command line.
7. **`framac.contract_diff(file, baseline) → {ok, edits}`** — the
   anti-cheat check from §2.3, exposed as a callable tool so the
   agent can self-audit before declaring victory.

The point of running the bench is to *test* this list: which were
needed, which weren't, what's missing. Update §5's "Proposed MCP
tools" against this hypothesis after the run.

## 7. Step-by-step

1. **Smoke test on `gcd`** end-to-end via one Agent call. Confirm:
   - subagent finds `frama-c` on `PATH`,
   - it edits the file in its worktree,
   - it returns the expected JSON shape,
   - the diff check is clean.
2. **Vacuity probe** across all 77 (§4). Block on clean.
3. **Pilot batch — 5 problems** chosen for phase coverage:
   `gcd` (P1, simple), `binary_search` (no prior port), `bubble_sort`
   (P1 + permutation spec), `dijkstra` (P2+P3, heavy axiomatic),
   `bst_insert` (P2+P4, recursive datatype). Same 4-wide batch shape
   as the full run.
   Read the 5 transcripts carefully; refine the subagent prompt if
   anything is consistently confused (e.g. a hard rule was
   misinterpreted).
4. **Full run** — 77 problems, batches of 4, global 5 h cap.
5. **Analysis** — populate §5's failure-mode histogram and tool
   wishlist. This is a manual pass over 77 JSON files; budget ~1 h.
6. **Deliverable** — `results/acsl_session/summary.md` with the
   headline pass-rate and the proposed MCP tool list, ranked.

## 8. Pitfalls

- **The cap matters.** Without it, a single thrashing problem
  (`edmond_karp` with its mutable BFS predicates is a likely
  candidate) eats the global budget. Cap is enforced inside the
  subagent prompt; trust the agent on it.
- **Failed attempts are also data.** Even on `failed` / `gave_up`
  verdicts, keep the final `algoveri_solution/<name>/acsl_spec.c` —
  the friction journal references it. Don't reset the workspace until
  after the analysis pass in §5.
- **Frama-C output truncation.** Even at 10s timeout, a failed run
  can spew 30+ KB. The subagent prompt should encourage `grep -E
  "^\[wp\]"` filtering. If many subagents flag this, MCP tool #1
  jumps to top of the list.
- **Honest reporting.** `friction_journal` is self-reported by the
  same agent that solves the problem, so there's a bias toward "the
  task was easy" once it succeeds. Counter: read the transcripts, not
  just the journal field.
- **The numbers won't be apples-to-apples** with the paper (different
  harness shape, agent vs. single-completion). Frame the headline
  accordingly in §5's deliverable.

## 9. Out of scope

- Re-running Dafny / Verus / Lean under this same agent harness
  (would make the comparison apples-to-apples — possible follow-up).
- Building the MCP tools themselves. This run discovers *which* to
  build; that's the next session's work.
- The `src/verifiers/acsl_verifier.py` integration
  (`ACSL_INTEGRATION_PLAN.md`).

## 10. Deliverable

`results/acsl_session/summary.md` containing:
- baseline pass-rate `X / 77`,
- per-category breakdown,
- failure-mode histogram,
- ranked MCP-tool proposal with API sketches and expected uplift.
