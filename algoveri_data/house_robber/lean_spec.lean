import Mathlib

def seq_u64_to_int (xs : List Nat) : List Nat := xs

-- !benchmark @start auxcode
def is_valid_robbery (houses : List Nat) (len : Nat) : Prop :=
  (∀ i, i < houses.length → houses.getD i 0 < len) ∧
  (∀ i, i < houses.length - 1 → houses.getD (i+1) 0 ≥ houses.getD i 0 + 2)

def total_loot (houses : List Nat) (values : List Nat) : Nat :=
  houses.foldl (fun acc i => acc + values.getD i 0) 0
-- !benchmark @end auxcode

-- Precondition definition
@[simp, reducible]
def rob_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  nums.length ≤ 100 ∧
  ∀ i, i < nums.length → nums.getD i 0 ≤ 10000
  -- !benchmark @end precond

-- Main function (dynamic programming solution)
def rob (nums : List Nat) (h_precond : rob_precond nums) : Nat :=
  -- !benchmark @start code
  let rec go (xs : List Nat) (prev2 prev1 : Nat) : Nat :=
    match xs with
    | [] => prev1
    | x :: xs' =>
        let cand := prev2 + x
        let new_max := if prev1 > cand then prev1 else cand
        go xs' prev1 new_max
  go nums 0 0
  -- !benchmark @end code

-- Postcondition definition
@[simp, reducible]
def rob_postcond (nums : List Nat) (result : Nat) (h_precond : rob_precond nums) : Prop :=
  -- !benchmark @start postcond
  (∀ houses : List Nat,
      is_valid_robbery houses nums.length →
        total_loot houses (seq_u64_to_int nums) ≤ result) ∧
    (∃ houses : List Nat,
        is_valid_robbery houses nums.length ∧
          total_loot houses (seq_u64_to_int nums) = result)
  -- !benchmark @end postcond

-- !benchmark @start lemma
-- !benchmark @end lemma

-- Proof that the implementation satisfies the postcondition
theorem rob_postcond_satisfied (nums : List Nat) (h_precond : rob_precond nums) :
    rob_postcond nums (rob nums h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
