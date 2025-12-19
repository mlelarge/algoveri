use vstd::prelude::*;

verus! {
    // Following is the block for necessary definitions
    // <preamble>
    spec fn is_sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
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
    // </preamble>

    // Following is the block for potential helper specifications
    // <helpers>
    proof fn lemma_permutation_identity(v: Seq<i32>)
        ensures is_permutation(v, v)
    {
        let n = v.len() as int;
        let p = Seq::new(n as nat, |i: int| i);
        assert(is_valid_index_permutation(p, n));
        assert(forall|i: int| 0 <= i < n ==> v[i] == v[#[trigger] p[i]]);
        assert(exists|ps: Seq<int>| is_valid_index_permutation(ps, n) && (forall|i: int| 0 <= i < n ==> v[i] == v[#[trigger] ps[i]]));
    }

    proof fn lemma_permutation_swap(v1: Seq<i32>, v2: Seq<i32>, i: int, j: int)
        requires
            v1.len() == v2.len(),
            0 <= i < v1.len(),
            0 <= j < v1.len(),
            v2 == v1.update(i, v1[j]).update(j, v1[i])
        ensures is_permutation(v1, v2)
    {
        let n = v1.len() as int;
        let p = Seq::new(n as nat, |k: int| if k == i { j } else if k == j { i } else { k });
        assert(is_valid_index_permutation(p, n));
        assert(forall|k: int| 0 <= k < n ==> v2[k] == v1[#[trigger] p[k]]);
        assert(exists|ps: Seq<int>| is_valid_index_permutation(ps, n) && (forall|k: int| 0 <= k < n ==> v2[k] == v1[#[trigger] ps[k]]));
    }

    proof fn lemma_permutation_transitive(v1: Seq<i32>, v2: Seq<i32>, v3: Seq<i32>)
        requires is_permutation(v1, v2), is_permutation(v2, v3)
        ensures is_permutation(v1, v3)
    {
        let p1 = choose|p1: Seq<int>| is_valid_index_permutation(p1, v1.len() as int) && (forall|k: int| 0 <= k < v1.len() ==> v2[k] == v1[#[trigger] p1[k]]);
        let p2 = choose|p2: Seq<int>| is_valid_index_permutation(p2, v2.len() as int) && (forall|k: int| 0 <= k < v2.len() ==> v3[k] == v2[#[trigger] p2[k]]);
        let n = v1.len() as int;
        let p3 = Seq::new(n as nat, |k: int| p1[p2[k]]);
        
        assert(is_valid_index_permutation(p3, n)) by {
            assert(p3.len() == n);
            assert(forall|k: int| 0 <= k < n ==> 0 <= #[trigger] p3[k] < n);
            assert forall|k1: int, k2: int| 0 <= k1 < k2 < n implies #[trigger] p3[k1] != #[trigger] p3[k2] by {
                let a = p2[k1];
                let b = p2[k2];
                // Since p2 is valid, a != b
                if a < b {
                    assert(p1[a] != p1[b]);
                } else if b < a {
                    assert(p1[b] != p1[a]);
                }
            }
        }
        assert(forall|k: int| 0 <= k < n ==> v3[k] == v1[#[trigger] p3[k]]);
        assert(exists|p: Seq<int>| is_valid_index_permutation(p, n) && (forall|k: int| 0 <= k < n ==> v3[k] == v1[#[trigger] p[k]]));
    }
    // </helpers>

    // Following is the block for proofs of lemmas, or functions that help the implementation or verification of the main specification
    // <proofs>

    // </proofs>

    // Following is the block for the main specification
    // <spec>
    fn bubble_sort(v: &mut Vec<i32>)
        ensures
            is_sorted(v@),
            is_permutation(old(v)@, v@),
    // </spec>
    // <code>
    {
        let n = v.len();
        if n <= 1 {
            proof {
                lemma_permutation_identity(v@);
            }
            return;
        }

        proof {
            lemma_permutation_identity(v@);
        }

        for i in 0..n
            invariant
                v.len() == n,
                is_permutation(old(v)@, v@),
                // The suffix [n-i..n] is sorted
                forall|k1: int, k2: int| (n as int - i as int) <= k1 < k2 < n as int ==> #[trigger] v@[k1] <= #[trigger] v@[k2],
                // All elements in the unsorted prefix are <= every element in the sorted suffix
                forall|k1: int, k2: int| 0 <= k1 < (n as int - i as int) && (n as int - i as int) <= k2 < n as int ==> #[trigger] v@[k1] <= #[trigger] v@[k2],
        {
            let upper_j = n - 1 - i;
            for j in 0..upper_j
                invariant
                    v.len() == n,
                    0 <= i < n,
                    upper_j == n - 1 - i,
                    0 <= j <= upper_j,
                    is_permutation(old(v)@, v@),
                    // Suffix properties are maintained during the inner loop
                    forall|k1: int, k2: int| (n as int - i as int) <= k1 < k2 < n as int ==> #[trigger] v@[k1] <= #[trigger] v@[k2],
                    forall|k1: int, k2: int| 0 <= k1 < (n as int - i as int) && (n as int - i as int) <= k2 < n as int ==> #[trigger] v@[k1] <= #[trigger] v@[k2],
                    // v[j] is the maximum element encountered so far in this pass
                    forall|k: int| 0 <= k < j ==> #[trigger] v@[k] <= v@[j as int],
            {
                let val_j = v[j];
                let val_j1 = v[j + 1];
                if val_j > val_j1 {
                    let ghost v_before_swap = v@;
                    v.set(j, val_j1);
                    v.set(j + 1, val_j);
                    proof {
                        lemma_permutation_swap(v_before_swap, v@, j as int, (j + 1) as int);
                        lemma_permutation_transitive(old(v)@, v_before_swap, v@);
                    }
                }
                assert(forall|k: int| 0 <= k < (j + 1) ==> #[trigger] v@[k] <= v@[(j + 1) as int]);
            }
            // After inner loop, v[n-1-i] is the max of v[0..n-i].
            // This allows us to extend the sorted suffix by one element.
        }
    }
    // </code>

    #[verifier::external]
    fn main() {
        let mut v = vec![5, 1, 4, 2, 8];
        let ghost original_v = v@;
        
        bubble_sort(&mut v);
        
        assert(is_sorted(v@));
        assert(is_permutation(original_v, v@));
    }
}