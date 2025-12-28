from pathlib import Path

from src.verifiers.verus_verifier import VerusVerifier

code = """use vstd::prelude::*;

verus! {
    // Following is the block for necessary definitions
    // <preamble>
    spec fn is_sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
    }
    
    spec fn is_sorted_range(s: Seq<i32>, start: int, end: int) -> bool {
        forall|i: int, j: int| start <= i < j < end ==> s[i] <= s[j]
    }

    spec fn is_valid_index_permutation(p: Seq<int>, n: int) -> bool {
        &&& p.len() == n
        &&& (forall|i: int| 0 <= i < n ==> 0 <= #[trigger] p[i] < n)
        &&& (forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] p[i] != #[trigger] p[j])
    }

    spec fn is_permutation(v1: Seq<i32>, v2: Seq<i32>) -> bool {
        exists|p: Seq<int>| 
            is_valid_index_permutation(p, v1.len() as int) 
            && v1.len() == v2.len()
            && (forall|i: int| 0 <= i < v1.len() ==> v2[i] == v1[#[trigger] p[i]])
    }

    // Mathematical definition: "val" is the k-th smallest element of "s" if
    // the sorted version of "s" has "val" at index "k".
    spec fn is_kth_smallest(s: Seq<i32>, k: int, val: i32) -> bool {
        exists|sorted_s: Seq<i32>|
            is_permutation(s, sorted_s)
            // Manual trigger added here to satisfy the solver without warning
            && #[trigger] is_sorted(sorted_s)
            && 0 <= k < s.len()
            && sorted_s[k] == val
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
    fn kmp_search(haystack: &Vec<u8>, needle: &Vec<u8>) -> (indices: Vec<usize>)
        ensures
            // Soundness: Every index returned is a valid match
            forall|i: int| 0 <= i < indices.len() ==> 
                matches_at(haystack@, needle@, #[trigger] indices[i] as int),
            // Completeness: Every valid match in the haystack is found
            forall|i: int| #[trigger] matches_at(haystack@, needle@, i) ==> 
                exists|k: int| 0 <= k < indices.len() && indices[k] == i
    // </spec>
    // <code>
    {
        assume(false);
        vec![]
    }

    #[verifier::external]
    fn main() {
        let haystack = vec![0u8, 1, 2, 1, 2, 3]; // "012123"
        let needle = vec![1u8, 2];               // "12"
        
        let indices = kmp_search(&haystack, &needle);
        
        // Should find matches at index 1 and 3
        assert(indices.len() == 2); 
    }
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
