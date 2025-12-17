from pathlib import Path

from src.verifiers.dafny_verifier import DafnyVerifier

code = """// <preamble>
predicate is_sorted(s: seq<int>) {
    forall i: int, j: int :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}
// </preamble>

// <helpers>
// </helpers>

// <proofs>
// </proofs>

// <spec>
method binary_search_lower_bound(s: seq<int>, target: int) returns (result: int)
    requires |s| <= 0x7FFFFFFF
    requires is_sorted(s)
    // We must ensure result is non-negative so the index access s[i] 
    // in the last postcondition is well-formed.
    ensures 0 <= result <= |s|
    ensures forall i: int :: 0 <= i < result ==> s[i] < target
    ensures forall i: int :: result <= i < |s| ==> s[i] >= target
// </spec>

// <code>
{
    var low := 0;
    var high := |s|;

    while low < high
        invariant 0 <= low <= high <= |s|
        invariant forall i :: 0 <= i < low ==> s[i] < target
        invariant forall i :: high <= i < |s| ==> s[i] >= target
    {
        var mid := low + (high - low) / 2;
        if s[mid] < target {
            low := mid + 1;
        } else {
            high := mid;
        }
    }
    return low;
}
// </code>"""

def test_dafny_verifier_writes_file_and_returns_result():
    """Verify that LeanVerifier writes the source file and returns a result dict.

    This test uses `test/config_test.yaml` (created as part of the test suite).
    """
    cfg_path = Path(__file__).resolve().parent / "config_test.yaml"
    verifier = DafnyVerifier(config_path=str(cfg_path))

    sample_source = code
    result = verifier.verify(source=sample_source, spec="", filename="unit_test")

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
