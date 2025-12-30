import os

PROMPT = """You are an expert in formal verification, specifically specializing in translating specifications and proofs between **Verus (Rust)** and **Dafny**. Your goal is to translate a Verus verification benchmark (code + natural language description) into an equivalent Dafny benchmark.

**Input Format:**
You will receive two parts:
1. **Verus Code:** A code block containing specific XML-like tags (`<preamble>`, `<helpers>`, `<proofs>`, `<spec>`, `<code>`).
2. **Natural Language Description:** A paragraph describing the algorithm and the verification goal.

**Output Format:**
You must provide:
1. **Dafny Code:** A syntactically correct Dafny translation maintaining the same logic and XML-like tag structure.
2. **Adapted Description:** The natural language description rewritten to match Dafny terminology (e.g., replacing "Verus" with "Dafny", "Vector" with "Sequence").

**Translation Guidelines:**

1.  **Type Mapping & Implicit Constraints (CRITICAL):**
    * Verus `bool` $\rightarrow$ Dafny `bool`.
    * Verus `Seq<T>` or `&Vec<T>` $\rightarrow$ Dafny `seq<T>`.
    * **Unsigned Integers (`usize`, `u32`):** Translate these to Dafny `int`.
    * **Constraint Rule:** Since Dafny `int` is signed (can be negative), you **must explicitly add** `requires arg >= 0` or `ensures result >= 0` if the original Verus type was unsigned (`usize`).
        * *Example:* `fn foo() -> (r: usize)` becomes `method foo() returns (r: int) ensures r >= 0`.

2.  **Ghost & Proof Handling:**
    * **Ghost Variables:** Verus `ghost var x` $\rightarrow$ Dafny `ghost var x`.
    * **Tracked Variables:** Verus `tracked var x` $\rightarrow$ Dafny `ghost var x` (Dafny treats linear resources as ghost state; add a comment `// Note: Linearity check removed`).
    * **Proof Blocks:** Verus `proof { ... }` blocks inside methods should be **unwrapped**. Dafny mixes ghost and executable statements freely. Just place the statements directly in the body.
    * **Ghost Functions:** Verus `ghost fn` $\rightarrow$ Dafny `ghost function` (if pure) or `ghost method`.

3.  **Function Mapping:**
    * Verus `spec fn` $\rightarrow$ Dafny `function` or `predicate` (if returning bool).
    * Verus `fn` (executable) $\rightarrow$ Dafny `method`.
    * Verus `check`, `assert` $\rightarrow$ Dafny `assert`.

4.  **Quantifiers & Logic:**
    * Verus `forall|i: int|` $\rightarrow$ Dafny `forall i ::`.
    * Verus `seq.len()` $\rightarrow$ Dafny `|seq|`.
    * Verus `seq[i]` $\rightarrow$ Dafny `seq[i]`.
    * **Triggers:** Convert `#[trigger seq[i]]` to `{seq[i]}` at the end of the quantifier body.

5.  **Structure:**
    * Remove `use vstd::prelude::*;` and `verus! {}` wrappers.
    * Keep the `<preamble>`, `<spec>`, `<proofs>`, and `<code>` comments to structure the output.

Now, I will give you the verus specification (without proof) and the natural language description. Please provide the Dafny translation and adapted description.

"""

TEMPLATE="```verus\n{code}\n```\n\n```txt\n{description}\n```"

def translate_to_dafny_prompt(verus_code: str, description: str) -> str:
    prompt = PROMPT + TEMPLATE.format(code=verus_code, description=description)
    return prompt

def translate_to_dafny_problem(path):
    verus_file = os.path.join(path, "verus_spec.rs")
    description_file = os.path.join(path, "verus_nl.txt")
    with open(verus_file, "r") as vf:
        verus_code = vf.read()
    with open(description_file, "r") as df:
        description = df.read()
    return translate_to_dafny_prompt(verus_code, description)

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Usage: python translate_to_dafny.py <path_to_benchmark>")
        sys.exit(1)
    path = sys.argv[1]
    path = os.path.join('/scratch/gpfs/ARORA/haoyu/algoveri/algoveri_data', path)
    prompt = translate_to_dafny_problem(path)
    print(prompt)
