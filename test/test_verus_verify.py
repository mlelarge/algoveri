from pathlib import Path

from src.verifiers.verus_verifier import VerusVerifier

code = """use vstd::prelude::*;

verus! {
    // Following is the block for necessary definitions
    // <preamble>
    
    // Mathematical definition of divisibility:
    // d divides n if there exists some integer k such that d * k = n.
    pub open spec fn divides(d: nat, n: nat) -> bool {
        exists|k: nat| d * k == n
    }

    // Predicate defining the properties of the Greatest Common Divisor (g):
    // 1. g must be a common divisor of a and b.
    // 2. g must be greater than or equal to any other common divisor d.
    pub open spec fn is_gcd(g: nat, a: nat, b: nat) -> bool {
        &&& divides(g, a)
        &&& divides(g, b)
        &&& forall|d: nat| divides(d, a) && divides(d, b) ==> d <= g
    }

    // The declarative specification for GCD.
    // Instead of an algorithm, this describes WHAT the result is.
    // We handle the (0, 0) edge case explicitly (where "greatest" is undefined mathematically),
    // matching the behavior of standard implementations (returning 0).
    pub open spec fn spec_gcd(a: nat, b: nat) -> nat {
        if a == 0 && b == 0 {
            0
        } else {
            // "Choose the g such that g is the GCD of a and b"
            choose|g: nat| is_gcd(g, a, b)
        }
    }
    // </preamble>

    // Following is the block for potential helper specifications
    // <helpers>

    // </helpers>

    // Following is the block for proofs of lemmas
    // <proofs>

    // </proofs>

    // Following is the block for the main specification
    // <spec>
    fn compute_gcd(a: u64, b: u64) -> (res: u64)
        ensures
            // The postcondition ensures the result matches the mathematical "max" definition
            res == spec_gcd(a as nat, b as nat)
    // </spec>
    // <code>
    {
        // Implement and verify the Euclidean algorithm to compute the GCD
        // (Note: You will now need proofs showing the Euclidean algorithm 
        // satisfies the mathematical properties defined in is_gcd)
        assume(false); // Placeholder
        0
    }
    // </code>

    fn main() {}
}"""

def test_verus_verifier_writes_file_and_returns_result():
    """Verify that VerusVerifier writes the source file and returns a result dict.

    This test uses `test/config_test.yaml` (created as part of the test suite).
    It does not require a working `verus` binary; it only asserts that the
    verifier produces a dict with expected keys and that the output file exists.
    """
    cfg_path = Path(__file__).resolve().parent / "config_jiawei_test.yaml"
    verifier = VerusVerifier(config_path=str(cfg_path))

    sample_source = code
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
    test_verus_verifier_writes_file_and_returns_result()
