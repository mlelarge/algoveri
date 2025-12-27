from pathlib import Path

from src.verifiers.verus_verifier import VerusVerifier

code = """use vstd::prelude::*;

verus! {
    // <preamble>
    // We define the GCD recursively. This serves as the "Ground Truth".
    // This definition mirrors the Euclidean algorithm, which is the standard
    // mathematical definition for computation.
    pub open spec fn spec_gcd(a: nat, b: nat) -> nat
        decreases b
    {
        if b == 0 {
            a
        } else {
            spec_gcd(b, a % b)
        }
    }
    // </preamble>

    // <helpers>

    // </helpers>

    // <spec>
    fn compute_gcd(a: u64, b: u64) -> (res: u64)
        ensures
            res == spec_gcd(a as nat, b as nat)
    // </spec>
    // <code>
    {
        assume(false);
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
