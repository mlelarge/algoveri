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
    /// Proves that any sequence is a permutation of itself (identity).
    proof fn lemma_identity_is_permutation(v: Seq<i32>)
        ensures is_permutation(v, v)
    {
        let n = v.len() as int;
        let p = Seq::new(v.len(), |i: int| i);
        assert(is_valid_index_permutation(p, n));
        assert(forall|i: int| 0 <= i < n ==> v[i] == v[#[trigger] p[i]]);
        assert(is_permutation(v, v));
    }

    /// Proves that swapping two elements in a sequence results in a permutation.
    proof fn lemma_swap_is_permutation(v1: Seq<i32>, i: int, j: int)
        requires 0 <= i < v1.len(), 0 <= j < v1.len()
        ensures is_permutation(v1, v1.update(i, v1[j]).update(j, v1[i]))
    {
        let n = v1.len() as int;
        let v2 = v1.update(i, v1[j]).update(j, v1[i]);
        let p = Seq::new(v1.len(), |k: int| if k == i { j } else if k == j { i } else { k });
        
        assert(is_valid_index_permutation(p, n)) by {
            assert forall|k1: int, k2: int| 0 <= k1 < k2 < n implies #[trigger] p[k1] != #[trigger] p[k2] by {}
        }
        assert(forall|k: int| 0 <= k < n ==> v2[k] == v1[#[trigger] p[k]]);
        assert(is_permutation(v1, v2));
    }

    /// Proves the transitivity of the is_permutation property.
    proof fn lemma_permutation_transitive(v1: Seq<i32>, v2: Seq<i32>, v3: Seq<i32>)
        requires is_permutation(v1, v2), is_permutation(v2, v3)
        ensures is_permutation(v1, v3)
    {
        let n = v1.len() as int;
        let p1 = choose|p1: Seq<int>| is_valid_index_permutation(p1, n) 
            && v1.len() == v2.len()
            && (forall|i: int| 0 <= i < n ==> v2[i] == v1[#[trigger] p1[i]]);
        let p2 = choose|p2: Seq<int>| is_valid_index_permutation(p2, n) 
            && v2.len() == v3.len()
            && (forall|i: int| 0 <= i < n ==> v3[i] == v2[#[trigger] p2[i]]);
        
        let p3 = Seq::new(v1.len(), |k: int| p1[p2[k]]);

        assert(is_valid_index_permutation(p3, n)) by {
            assert forall|i: int, k: int| 0 <= i < k < n implies #[trigger] p3[i] != #[trigger] p3[k] by {
                let pi = p2[i];
                let pk = p2[k];
                assert(pi != pk);
                assert(p1[pi] != p1[pk]);
            }
        }
        assert(forall|k: int| 0 <= k < n ==> v3[k] == v1[#[trigger] p3[k]]);
        assert(is_permutation(v1, v3));
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
        if n <= 1 {
            proof { lemma_identity_is_permutation(old(v)@); }
            return;
        }

        proof { lemma_identity_is_permutation(v@); }

        for i in 0..n
            invariant
                n == v.len(),
                0 <= i <= n,
                is_permutation(old(v)@, v@),
                is_sorted(v@.subrange(0, i as int)),
        {
            let mut j = i;
            // Help the solver bridge from the outer invariant to the inner loop start
            assert(is_sorted(v@.subrange(0, j as int)));
            assert(is_sorted(v@.subrange(j as int, (i + 1) as int)));
            
            while j > 0 && v[j-1] > v[j]
                invariant
                    n == v.len(),
                    0 <= j <= i < n,
                    is_permutation(old(v)@, v@),
                    // Invariants that describe the "almost sorted" state:
                    is_sorted(v@.subrange(0, j as int)),
                    is_sorted(v@.subrange(j as int, (i + 1) as int)),
                    // Elements to the left of the gap are smaller than elements to the right
                    forall|k1: int, k2: int| 0 <= k1 < j && j < k2 <= i ==> v@[k1] <= v@[k2],
            {
                let ghost v_old_inner = v@;
                let j_idx = j;
                let j_prev_idx = j - 1;
                
                // Swap manually to avoid overloaded deref issue
                let val_j = v[j_idx];
                let val_prev = v[j_prev_idx];
                v.set(j_idx, val_prev);
                v.set(j_prev_idx, val_j);

                proof {
                    lemma_swap_is_permutation(v_old_inner, j_prev_idx as int, j_idx as int);
                    lemma_permutation_transitive(old(v)@, v_old_inner, v@);
                }
                j -= 1;
            }

            // After the inner loop, prove the prefix [0..i+1] is fully sorted.
            assert forall|k1: int, k2: int| 0 <= k1 < k2 <= i implies v@[k1] <= v@[k2] by {
                let j_int = j as int;
                if k2 < j_int {
                    // Follows from is_sorted(v@.subrange(0, j))
                } else if k1 >= j_int {
                    // Follows from is_sorted(v@.subrange(j, i+1))
                } else {
                    // Crossing case: k1 < j <= k2.
                    if k2 == j_int {
                        // k1 < j and k2 = j. We need v[k1] <= v[j].
                        if k1 == j_int - 1 {
                            // Loop terminated or j=0. Since k1>=0, j>0, so v[j-1] <= v[j] holds.
                        } else {
                            // k1 < j-1. v[k1] <= v[j-1] (sorted prefix) and v[j-1] <= v[j].
                        }
                    } else {
                        // k1 < j and k2 > j. Follows from the cross-invariant.
                    }
                }
            }
            assert(is_sorted(v@.subrange(0, (i + 1) as int)));
        }
        // At the end, the subrange [0, n] is the whole sequence.
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