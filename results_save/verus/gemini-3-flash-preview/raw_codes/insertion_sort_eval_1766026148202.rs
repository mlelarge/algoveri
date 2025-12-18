use vstd::prelude::*;

verus! {
    // Following is the block for necessary definitions
    // <preamble>
    spec fn is_sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
    }

    spec fn is_valid_index_permutation(p: Seq<int>, n: int) -> bool {
        p.len() == n
        && (forall|i: int| 0 <= i < n ==> 0 <= #[trigger] p[i] < n)
        && (forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] p[i] != #[trigger] p[j])
    }

    spec fn is_permutation(v1: Seq<i32>, v2: Seq<i32>) -> bool {
        exists|p: Seq<int>| 
            is_valid_index_permutation(p, v1.len() as int) 
            && v1.len() == v2.len()
            && (forall|i: int| 0 <= i < v1.len() ==> v2[i] == v1[#[trigger] p[i]])
    }
    // </preamble>

    // Following is the block for potential helper specifications
    // <helpers>

    // </helpers>

    // Following is the block for proofs of lemmas, or functions that help the implementation or verification of the main specification
    // <proofs>
    /// Proves that any sequence is a permutation of itself (identity permutation).
    proof fn lemma_identity_is_permutation(v: Seq<i32>)
        ensures is_permutation(v, v)
    {
        let n = v.len();
        let p = Seq::new(n as nat, |i: int| i);
        assert(is_valid_index_permutation(p, n as int));
        assert(forall|i: int| 0 <= i < n ==> v[i] == v[#[trigger] p[i]]);
    }

    /// Proves that swapping two elements in a sequence results in a permutation.
    proof fn lemma_swap_is_permutation(v1: Seq<i32>, i: int, j: int)
        requires 0 <= i < v1.len(), 0 <= j < v1.len()
        ensures is_permutation(v1, v1.update(i, v1[j]).update(j, v1[i]))
    {
        let n = v1.len();
        let p = Seq::new(n as nat, |k: int| if k == i { j } else if k == j { i } else { k });
        let v2 = v1.update(i, v1[j]).update(j, v1[i]);
        assert(is_valid_index_permutation(p, n as int));
        assert(forall|k: int| 0 <= k < n ==> v2[k] == v1[#[trigger] p[k]]);
    }

    /// Proves the transitivity of the is_permutation relation.
    proof fn lemma_permutation_transitive(v1: Seq<i32>, v2: Seq<i32>, v3: Seq<i32>)
        requires is_permutation(v1, v2), is_permutation(v2, v3)
        ensures is_permutation(v1, v3)
    {
        let p1 = choose|p1: Seq<int>| is_valid_index_permutation(p1, v1.len() as int) && v1.len() == v2.len() && (forall|k: int| 0 <= k < v1.len() ==> v2[k] == v1[#[trigger] p1[k]]);
        let p2 = choose|p2: Seq<int>| is_valid_index_permutation(p2, v2.len() as int) && v2.len() == v3.len() && (forall|k: int| 0 <= k < v2.len() ==> v3[k] == v2[#[trigger] p2[k]]);
        let n = v1.len();
        let p3 = Seq::new(n as nat, |k: int| p1[p2[k]]);
        
        assert(is_valid_index_permutation(p3, n as int)) by {
            forall|k1: int, k2: int| 0 <= k1 < k2 < n as int ==> #[trigger] p3[k1] != #[trigger] p3[k2] {
                let a = p2[k1];
                let b = p2[k2];
                // Indices a and b are distinct because p2 is a permutation
                if a < b {
                    assert(p1[a] != p1[b]);
                } else {
                    assert(p1[b] != p1[a]);
                }
            }
        }
        assert(forall|k: int| 0 <= k < n ==> v3[k] == v1[#[trigger] p3[k]]);
    }
    // </proofs>

    // Following is the block for the main specification
    // <spec>
    fn insertion_sort(v: &mut Vec<i32>)
        ensures
            is_sorted(v@),
            is_permutation(old(v)@, v@),
    // </spec>
    // <code>
    {
        let n = v.len();
        if n == 0 {
            lemma_identity_is_permutation(old(v)@);
            return;
        }

        // Initially, the vector is a permutation of itself.
        lemma_identity_is_permutation(v@);
        
        // Outer loop: build the sorted prefix v[0..i]
        for i in 0..n
            invariant
                n == v.len(),
                0 <= i <= n,
                is_permutation(old(v)@, v@),
                is_sorted(v@.subrange(0, i as int)),
        {
            let mut j = i;
            // Inner loop: move the element v[i] into its correct sorted position
            while j > 0 && v[j-1] > v[j]
                invariant
                    n == v.len(),
                    0 <= i < n,
                    0 <= j <= i,
                    is_permutation(old(v)@, v@),
                    // Sequence is sorted if the "moving" element at index j is ignored
                    forall|k1: int, k2: int| 0 <= k1 < k2 <= i && k2 != j ==> v[k1] <= v[k2],
                    // All elements already shifted past j are >= the element at j
                    forall|k: int| j < k <= i ==> v[j] <= v[k],
            {
                let ghost v_old_inner = v@;
                v.swap(j-1, j);
                
                // Maintain the permutation property through the swap
                lemma_swap_is_permutation(v_old_inner, (j-1) as int, j as int);
                lemma_permutation_transitive(old(v)@, v_old_inner, v@);
                
                j -= 1;
            }

            // After the inner loop, verify that the prefix 0..i+1 is now fully sorted
            assert(forall|k1: int, k2: int| 0 <= k1 < k2 <= i ==> v[k1] <= v[k2]) by {
                forall|k1: int, k2: int| 0 <= k1 < k2 <= i ==> v[k1] <= v[k2] {
                    if k2 < j {
                        // Inherited from sortedness before j
                    } else if k2 == j {
                        if k1 < j - 1 {
                            // v[k1] <= v[j-1] and v[j-1] <= v[j]
                        } else {
                            // k1 == j-1, and v[j-1] <= v[j] is the loop termination condition
                        }
                    } else { // k2 > j
                        if k1 <= j {
                            // v[k1] <= v[j] or v[k1] <= v[k2] via invariant
                        } else {
                            // k1 > j, handled by the "almost sorted" invariant
                        }
                    }
                }
            }
            // Bridge the local sortedness to the prefix specification
            assert(is_sorted(v@.subrange(0, (i + 1) as int)));
        }
        // At the end, the subrange 0..n is the whole vector.
        assert(v@.subrange(0, n as int) =~= v@);
    }
    // </code>

    #[verifier::external]
    fn main() {
        let mut v = vec![5, 1, 4, 2, 8];
        let ghost original_v = v@;
        
        insertion_sort(&mut v);
        
        assert(is_sorted(v@));
        assert(is_permutation(original_v, v@));
    }
}