# ACSL integration — wiring plan

What's left to plug ACSL into the AlgoVeri harness as the fourth verifier
alongside Dafny / Verus / Lean.

## Status

**Done**:

- 77 `algoveri_data/<name>/acsl_spec.c` files in place (provenance:
  [ACSL_REALIGNMENT.md](ACSL_REALIGNMENT.md)).
- `scripts/apptainer_setup/acsl.def` — Apptainer recipe (Ubuntu 22.04 + opam
  Frama-C 32 / Alt-Ergo 2.6.2 / Why3 1.8.2 / pinned Z3 4.12.5 binary).
- `scripts/apptainer_setup/acsl.sh` — build helper, mirrors `verus.sh` /
  `dafny.sh` / `lean.sh`.

**Pending** (this doc): two new files to author from templates, three
existing files to extend.

## 1. Author from templates

### 1.1 `src/verifiers/acsl_verifier.py`

Copy [src/verifiers/verus_verifier.py](src/verifiers/verus_verifier.py) and
swap the Verus / Rust toolchain calls for the Frama-C / WP equivalents:

- Replace the per-source-file invocation (currently `verus <file>`) with
  `frama-c -wp -wp-timeout 10 -wp-prover alt-ergo,z3 -wp-par 4 <file>`.
- The Apptainer command in `_build_command` simplifies a lot — no
  `CARGO_HOME` / `RUSTUP_HOME` env, no `rust_home/cargo` and
  `rust_home/toolchains` binds. Just bind the host workdir:
  ```
  apptainer exec --bind <host_workdir>:/work <image_path> \
      frama-c -wp -wp-timeout 10 -wp-prover alt-ergo,z3 -wp-par 4 /work/<file>
  ```
- Output filename should be `<safe_name>_<ts>.c` (not `.rs`).
- Read config from `self.config.get("acsl", {})` instead of `verus`; the
  `apptainer.image_path` is the only required key (no `rust_home`).

### 1.2 `src/eval/acsl_eval.py`

Copy [src/eval/verus_eval.py](src/eval/verus_eval.py) (or pick whichever of
the three existing eval modules has the cleanest structure for your
purposes) and:

- Change the language tag from `verus` to `acsl`.
- Change the spec filename from `verus_spec.rs` to `acsl_spec.c`.
- Swap the result parser. The ACSL pass criterion is "every WP goal proved",
  which Frama-C reports as a single line:
  ```
  [wp] Proved goals:    N / N
  ```
  Pass condition: regex match `^\[wp\] Proved goals:\s+(\d+)\s*/\s*(\d+)`
  with the two numbers equal. Treat any other line as failure (no proved
  line at all = parse error or front-end failure).
- Surface the unproved-goal count when the run is partial — useful for
  triage of "almost there" cases.

## 2. Extend

### 2.1 `config/config.yaml`

Add an `acsl:` section mirroring the existing `verus:` block:

```yaml
acsl:
  method: "apptainer"
  timeout: 60
  apptainer:
    image_path: "YOUR_WORKING_DIR/apptainer_imgs/acsl.sif"

  local:
    bin_path: "/usr/local/bin/frama-c"
```

No `rust_home` / `elan_home` / `project_path` keys — Frama-C is
self-contained inside the image.

### 2.2 `src/run_task.py`

Currently the file imports `VerusEval` directly:

```python
from src.eval.verus_eval import VerusEval
```

(see `src/run_task.py:5`). Mirror it with:

```python
from src.eval.acsl_eval import AcslEval
```

and add `acsl` as an accepted value of `args.language`. Check
`src/eval/runner.py` — the `Runner` constructor takes `language=` and
likely has its own dispatch on the language tag; add `"acsl"` there too.

### 2.3 `VERIFIER_README.md`

Add an "ACSL" section after "Lean" with the build command:

```sh
# cd apptainer_imgs if not already there
apptainer build acsl.sif <repo_root>/scripts/apptainer_setup/acsl.def
# or: bash <repo_root>/scripts/apptainer_setup/acsl.sh
```

No post-build install dance (unlike Rust+Verus, which needs the rustup
bootstrap into `rust_home/`). The image ships everything.

## Smoke-test order

After all five items are in place, the fastest end-to-end check:

```sh
# Single-file verifier sanity check (no model in the loop)
apptainer exec --bind $(pwd):/work apptainer_imgs/acsl.sif \
    frama-c -wp -wp-timeout 10 -wp-prover alt-ergo,z3 -wp-par 4 \
            /work/algoveri_data/gcd/acsl_spec.c

# Single-problem AlgoVeri run with a cheap model
python -m src.run_task --language acsl --model gpt-5 \
    --cfg_path config/config.yaml --problem gcd
```

If `gcd` works end-to-end, run the full 1×15 budget across all 77 problems.
