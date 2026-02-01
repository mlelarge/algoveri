from pathlib import Path

from src.verifiers.dafny_verifier import DafnyVerifier

code = """// Following is the block for necessary definitions
// <preamble>
// Define u64 to enforce the safety constraint (overflow checks)
newtype u64 = x | 0 <= x < 0x1_0000_0000_0000_0000

// Pure mathematical definition of power on unbounded integers
function spec_pow(b: int, e: int): int
  requires e >= 0
  decreases e
{
  if e == 0 then
    1
  else
    b * spec_pow(b, e - 1)
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
method exponentiation(b: u64, e: u64) returns (res: u64)
  // Precondition: Result fits in u64 (0xffff_ffff_ffff_ffff)
  requires spec_pow(b as int, e as int) <= 0xffff_ffff_ffff_ffff
  
  ensures res as int == spec_pow(b as int, e as int)
// </spec>
// <code>
{
  // "assume false" creates a contradiction, implying everything follows.
  // The verifier will mark this as valid, ignoring missing assignments or proofs.
  assume false; 
}
// </code>
method Main() {
  // Empty main
}"""

def test_dafny_verifier_writes_file_and_returns_result():
    """Verify that LeanVerifier writes the source file and returns a result dict.

    This test uses `test/config_test.yaml` (created as part of the test suite).
    """
    cfg_path = Path(__file__).resolve().parent / "config_test.yaml"
    verifier = DafnyVerifier(config_path=str(cfg_path))

    sample_source = code
    result = verifier.verify(source=sample_source, spec="test", filename="unit_test")

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
    test_dafny_verifier_writes_file_and_returns_result()
