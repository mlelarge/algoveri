from pathlib import Path

from src.verifiers.dafny_verifier import DafnyVerifier

code = """// <preamble>
predicate is_sorted(s: seq<int>) {
    forall i: int, j: int {:trigger s[i], s[j]} :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}
// </preamble>

// <helpers>
// </helpers>

// <proofs>
// </proofs>

// <spec>
method linear_search_lower_bound(s: seq<int>, target: int) returns (result: int)
    requires |s| <= 0x7FFFFFFF
    requires is_sorted(s)
    ensures result >= 0
    ensures result <= |s|
    ensures forall i {:trigger s[i]} :: 0 <= i < result ==> s[i] < target
    ensures forall i {:trigger s[i]} :: result <= i < |s| ==> s[i] >= target
// </spec>
// <code>
{
    assume {:axiom} false;
}
// </code>

method main() {}"""

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
