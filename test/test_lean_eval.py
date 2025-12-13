from pathlib import Path

from src.eval.lean_eval import LeanEval
from src.llm.providers import GeminiProvider, OpenAICompatibleProvider, VLLMProvider
from src.verifiers.lean_verifier import LeanVerifier


problem1 = "import Mathlib\n\n-- Precondition definitions\n@[reducible, simp]\ndef goodWorkers_precond (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat) : Prop :=\n  -- !benchmark @start precond\n  records.length \u2264 4000 \u2227\n  \u2200 r \u2208 records, (r.2.1 \u2264 1_000_000) \u2227 (r.2.2 \u2264 100_000)\n  -- !benchmark @end precond\n\n\n-- Postcondition auxiliary definitions\ndef totalSales (records : List (Nat \u00d7 Nat \u00d7 Nat)) (id : Nat) : Nat :=\n  records.foldl (fun acc r => if r.1 = id then acc + r.2.1 * r.2.2 else acc) 0\n\ndef distinctIds (records : List (Nat \u00d7 Nat \u00d7 Nat)) : List Nat :=\n  records.foldl (fun acc r => if r.1 \u2208 acc then acc else acc ++ [r.1]) []\n\ndef qualifyingIds (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat) : List Nat :=\n  (distinctIds records).filter (fun i => totalSales records i \u2265 threshold)\n\n\n-- Main function definitions\ndef goodWorkers (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat)\n    (h_precond : goodWorkers_precond records threshold) : List Nat :=\n  -- !benchmark @start code\n  qualifyingIds records threshold\n  -- !benchmark @end code\n\n\n-- Postcondition definitions\n@[reducible, simp]\ndef goodWorkers_postcond (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat)\n    (result : List Nat) (h_precond : goodWorkers_precond records threshold) : Prop :=\n  -- !benchmark @start postcond\n  result = qualifyingIds records threshold\n  -- !benchmark @end postcond\n\n\n-- Proof content\ntheorem goodWorkers_postcond_satisfied (records : List (Nat \u00d7 Nat \u00d7 Nat)) (threshold : Nat)\n    (h_precond : goodWorkers_precond records threshold) :\n    goodWorkers_postcond records threshold (goodWorkers records threshold h_precond) h_precond := by\n  -- !benchmark @start proof\n  sorry\n  -- !benchmark @end proof"

problem2 = "import Mathlib\n\n-- Precondition definitions\n@[reducible, simp]\ndef maxSumSubmatrix_precond (n : Nat) (a : List (List Int)) : Prop :=\n  (1 \u2264 n) \u2227 (n \u2264 100) \u2227 (a.length = n) \u2227\n    (\u2200 row, row \u2208 a \u2192 row.length = n) \u2227\n    (\u2200 row, row \u2208 a \u2192 \u2200 v, v \u2208 row \u2192 ((-10000 : Int) \u2264 v \u2227 v \u2264 10000))\n\n-- Helper function: Kadane's algorithm for maximum sub\u2011array sum (non\u2011empty).\ndef kadane (arr : List Int) : Int :=\n  match arr with\n  | [] => 0\n  | x :: xs =>\n    let rec go (lst : List Int) (cur best : Int) : Int :=\n      match lst with\n      | [] => best\n      | y :: ys =>\n        let newCur := max y (cur + y)\n        let newBest := max best newCur\n        go ys newCur newBest\n    go xs x x\n\n-- Main function\ndef maxSumSubmatrix (n : Nat) (a : List (List Int))\n    (h_precond : maxSumSubmatrix_precond n a) : Int :=\n  -- we assume the precondition `h_precond` holds, so the matrix dimensions are correct.\n  let zeroList : List Int := List.replicate n 0\n  let initMax : Int := (-1000000000 : Int)\n\n  (List.range n).foldl (fun (maxSoFar : Int) (i : Nat) =>\n    let (_, newMax) :=\n      (List.range (n - i)).foldl (fun (state : List Int \u00d7 Int) (offset : Nat) =>\n        let (colSums, curMax) := state\n        let rowIdx := i + offset\n        let row := a.get! rowIdx\n        let newSums : List Int := List.zipWith (fun x y => x + y) colSums row\n        let subMax : Int := kadane newSums\n        (newSums, max curMax subMax)\n      ) (zeroList, maxSoFar)\n    newMax\n  ) initMax\n\n-- Sum of a sub\u2011matrix (indices are assumed to satisfy the bounds).\ndef submatrixSum (a : List (List Int)) (n i1 i2 j1 j2 : Nat) : Int :=\n  ((List.range (i2 + 1 - i1)).foldl (fun acc i =>\n    let row := a.get! (i1 + i)\n    let rowSum := ((List.range (j2 + 1 - j1)).foldl (fun rAcc j => rAcc + row.get! (j1 + j)) 0)\n    acc + rowSum) 0)\n\n-- Postcondition definitions\n@[reducible, simp]\ndef maxSumSubmatrix_postcond (n : Nat) (a : List (List Int)) (result : Int)\n    (h_precond : maxSumSubmatrix_precond n a) : Prop :=\n  (\u2200 i1 i2 j1 j2,\n      i1 \u2264 i2 \u2192 i2 < n \u2192 j1 \u2264 j2 \u2192 j2 < n \u2192\n      result \u2265 submatrixSum a n i1 i2 j1 j2) \u2227\n  (\u2203 i1 i2 j1 j2,\n      i1 \u2264 i2 \u2227 i2 < n \u2227 j1 \u2264 j2 \u2227 j2 < n \u2227\n      result = submatrixSum a n i1 i2 j1 j2)\n\n-- Proof that the implementation satisfies the postcondition\ntheorem maxSumSubmatrix_postcond_satisfied (n : Nat) (a : List (List Int))\n    (h_precond : maxSumSubmatrix_precond n a) :\n    maxSumSubmatrix_postcond n a (maxSumSubmatrix n a h_precond) h_precond := by\n  -- The detailed proof is omitted (placeholder).\n  sorry"


def demo():
    provider = OpenAICompatibleProvider()


    cfg_path = Path(__file__).resolve().parent / "config_jiawei_test.yaml"
    verifier = LeanVerifier(config_path=str(cfg_path))


    eval = LeanEval(llm_client=provider, verifier=verifier, max_rounds=3)
    res = eval.run_single(problem=problem2, model="gpt-4o", filename="test-lean-eval")
    print(res)


if __name__ == '__main__':
    demo()
