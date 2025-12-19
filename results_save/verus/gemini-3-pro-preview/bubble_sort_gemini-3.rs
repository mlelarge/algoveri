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
    spec fn perm_id(n: int) -> Seq<int> {
        Seq::new(n as nat, |i: int| i)
    }

    spec fn perm_swap(n: int, i: int, j: int) -> Seq<int> {
        Seq::new(n as nat, |k: int| {
            if k == i { j }
            else if k == j { i }
            else { k }
        })
    }

    spec fn perm_compose(p1: Seq<int>, p2: Seq<int>) -> Seq<int> {
        Seq::new(p2.len(), |i: int| p1[p2[i]])
    }
    // </helpers>

    // Following is the block for proofs of lemmas, or functions that help the implementation or verification of the main specification
    // <proofs>
    proof fn lemma_perm_refl(v: Seq<i32>)
        ensures is_permutation(v, v)
    {
        let p = perm_id(v.len() as int);
        assert(is_valid_index_permutation(p, v.len() as int));
        assert(is_permutation(v, v));
    }

    proof fn lemma_perm_swap(v1: Seq<i32>, v2: Seq<i32>, i: int, j: int)
        requires
            0 <= i < v1.len(),
            0 <= j < v1.len(),
            i != j,
            v2 == v1.update(i, v1[j]).update(j, v1[i]),
        ensures is_permutation(v1, v2)
    {
        let n = v1.len() as int;
        let p = perm_swap(n, i, j);
        
        assert(p.len() == n);
        // Added trigger p[k] to help quantifier instantiation
        assert(forall|k: int| 0 <= k < n ==> 0 <= #[trigger] p[k] < n);
        
        // Added trigger p[k1], p[k2] for injectivity
        assert(forall|k1: int, k2: int| 0 <= k1 < k2 < n ==> #[trigger] p[k1] != #[trigger] p[k2]); 
        
        assert(is_valid_index_permutation(p, n));
        assert(forall|k: int| 0 <= k < n ==> v2[k] == v1[#[trigger] p[k]]);
        assert(is_permutation(v1, v2));
    }

    proof fn lemma_perm_trans(v1: Seq<i32>, v2: Seq<i32>, v3: Seq<i32>)
        requires is_permutation(v1, v2), is_permutation(v2, v3)
        ensures is_permutation(v1, v3)
    {
        let p12 = choose|p: Seq<int>| is_valid_index_permutation(p, v1.len() as int) 
                && v1.len() == v2.len()
                && (forall|i: int| 0 <= i < v1.len() ==> v2[i] == v1[p[i]]);
        let p23 = choose|p: Seq<int>| is_valid_index_permutation(p, v2.len() as int) 
                && v2.len() == v3.len()
                && (forall|i: int| 0 <= i < v2.len() ==> v3[i] == v2[p[i]]);
                
        let p13 = perm_compose(p12, p23);
        let n = v1.len() as int;
        
        assert(p13.len() == n);
        assert(forall|i: int| 0 <= i < n ==> 0 <= #[trigger] p13[i] < n);
        assert(forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] p13[i] != #[trigger] p13[j]); 
        
        assert(forall|i: int| 0 <= i < n ==> v3[i] == v1[#[trigger] p13[i]]);
        assert(is_valid_index_permutation(p13, n));
        assert(is_permutation(v1, v3));
    }
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
        let ghost v0 = v@;
        proof { lemma_perm_refl(v@); }
        
        for i in 0..n
            invariant
                n == v.len(),
                is_permutation(v0, v@),
                // The last i elements are sorted (Suffix sortedness)
                forall|a: int, b: int| n - i <= a < b < n ==> v@[a] <= v@[b],
                // The elements in the unsorted prefix are smaller than or equal to elements in sorted suffix (Partitioning)
                forall|a: int, b: int| 0 <= a < n - i <= b < n ==> v@[a] <= v@[b],
        {
            let limit = n - 1 - i;
            
            // Inner loop: bubbling the max element to the end of the unsorted part
            for j in 0..limit
                invariant
                    n == v.len(),
                    0 <= i < n,
                    limit == n - 1 - i,
                    is_permutation(v0, v@),
                    // Outer invariants maintained
                    forall|a: int, b: int| n - i <= a < b < n ==> v@[a] <= v@[b],
                    forall|a: int, b: int| 0 <= a < n - i <= b < n ==> v@[a] <= v@[b],
                    // Max-bubbling property: v[j] is the max of 0..j+1
                    forall|k: int| 0 <= k <= j ==> v@[k] <= v@[j as int],
            {
                let j_usize = j;
                let j_next = j + 1;
                
                if v[j_usize] > v[j_next] {
                    let ghost v_old = v@;
                    
                    // Manually swap to avoid implicit slice conversion issues
                    let temp = v[j_usize];
                    v.set(j_usize, v[j_next]);
                    v.set(j_next, temp);
                    
                    proof {
                        lemma_perm_swap(v_old, v@, j as int, j+1 as int);
                        lemma_perm_trans(v0, v_old, v@);
                    }
                }
            }
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