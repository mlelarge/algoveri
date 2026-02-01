from pathlib import Path
import sys

from src.verifiers.lean_verifier import LeanVerifier

code = """import Mathlib

-- Precondition definitions
@[reducible, simp]
def compute_gcd_precond (a b : UInt64) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

-- Mathematical definition of divisibility
def divides (d n : Nat) : Prop :=
  ∃ k, d * k = n

-- Predicate defining the properties of the Greatest Common Divisor
-- 1. Common divisor
-- 2. Greater than or equal to any other common divisor
def is_gcd (g a b : Nat) : Prop :=
  divides g a ∧
  divides g b ∧
  (∀ d, divides d a → divides d b → d ≤ g)

-- Lemma asserting that a GCD always exists (standard number theory result).
-- We omit the proof here ('sorry') to treat it as an axiom for the specification.
lemma gcd_exists (a b : Nat) : ∃ g, is_gcd g a b := sorry

-- The declarative specification.
-- It returns the value 'g' that satisfies the is_gcd predicate.
noncomputable def spec_gcd (a b : Nat) : Nat :=
  if a = 0 ∧ b = 0 then 0
  else Classical.choose (gcd_exists a b)

-- !benchmark @start auxcode
-- !benchmark @end auxcode

-- Main function definitions
def compute_gcd (a b : UInt64) (h_precond : compute_gcd_precond a b) : UInt64 :=
  -- !benchmark @start code
  sorry
  -- !benchmark @end code

-- Postcondition definitions
@[reducible, simp]
def compute_gcd_postcond (a b : UInt64) (result : UInt64) (h_precond : compute_gcd_precond a b) : Prop :=
  -- !benchmark @start postcond
  result.toNat = spec_gcd a.toNat b.toNat
  -- !benchmark @end postcond

-- !benchmark @start lemma
-- !benchmark @end lemma

-- Proof content
theorem compute_gcd_postcond_satisfied (a b : UInt64) (h_precond : compute_gcd_precond a b) :
    compute_gcd_postcond a b (compute_gcd a b h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

"""

def test_lean_verifier_writes_file_and_returns_result():
    """Verify that LeanVerifier writes the source file and returns a result dict.

    This test uses `test/config_test.yaml` (created as part of the test suite).
    """
    cfg_path = Path(__file__).resolve().parent / "config_test.yaml"
    verifier = LeanVerifier(config_path=str(cfg_path))

    # If the test is invoked with piped stdin, prefer that content as the
    # sample source. We only read stdin when it's not a TTY to avoid blocking
    # interactive runs.
    stdin_data = None
    try:
        if not sys.stdin.isatty():
            stdin_data = sys.stdin.read()
    except Exception:
        stdin_data = None

    sample_source = stdin_data if (stdin_data is not None and stdin_data.strip() != "") else code
    result = verifier.verify(source=sample_source, spec="dummy-spec", filename="unit_test")

    print(result)

    assert isinstance(result, dict)
    assert "ok" in result and isinstance(result["ok"], bool)
    assert "file" in result

    # The file should have been created on disk
    written = Path(result["file"])
    assert written.exists()
    return
    # cleanup artifact
    try:
        written.unlink()
    except Exception:
        pass

if __name__ == '__main__':
    test_lean_verifier_writes_file_and_returns_result()
