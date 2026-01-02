from pathlib import Path

from src.verifiers.dafny_verifier import DafnyVerifier

code = """// Following is the block for necessary definitions
// <preamble>
ghost predicate is_sorted(s: seq<int>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate is_valid_index_permutation(p: seq<int>, n: int) {
    && |p| == n
    && (forall i {:trigger p[i]} :: 0 <= i < n ==> 0 <= p[i] < n)
    && (forall i, j {:trigger p[i], p[j]} :: 0 <= i < j < n ==> p[i] != p[j])
}

ghost predicate is_permutation(v1: seq<int>, v2: seq<int>) {
    exists p: seq<int> :: 
        is_valid_index_permutation(p, |v1|) 
        && |v1| == |v2|
        && (forall i {:trigger p[i]} :: 0 <= i < |v1| ==> v2[i] == v1[p[i]])
}
// </preamble>

// Following is the block for potential helper specifications
// <helpers>
// </helpers>

// Following is the block for proofs of lemmas
// <proofs>
// </proofs>

// Following is the block for the main specification and implementation
// <spec>
method bubble_sort(v: seq<int>) returns (v_new: seq<int>)
    ensures is_sorted(v_new)
    ensures is_permutation(v, v_new)
// </spec>

// <code>
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
