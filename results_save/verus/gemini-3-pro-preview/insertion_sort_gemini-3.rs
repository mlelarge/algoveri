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
    spec fn sorted_range(v: Seq<i32>, start: int, end: int) -> bool {
        forall|i: int, j: int| start <= i < j < end ==> v[i] <= v[j]
    }
    // </helpers>

    // Following is the block for proofs of lemmas, or functions that help the implementation or verification of the main specification
    // <proofs>
    proof fn lemma_sorted_range_to_is_sorted(v: Seq<i32>, start: int, end: int)
        requires 
            0 <= start <= end <= v.len(),
            sorted_range(v, start, end),
        ensures is_sorted(v.subrange(start, end))
    {
        let s = v.subrange(start, end);
        assert forall|i: int, j: int| 0 <= i < j < s.len() implies s[i] <= s[j] by {
            // s[i] == v[start + i], s[j] == v[start + j]
            // start + i < start + j
        };
    }

    proof fn lemma_permutation_refl(v: Seq<i32>)
        ensures is_permutation(v, v)
    {
        let n = v.len() as int;
        let p = Seq::new(n as nat, |i: int| i);
        assert(is_valid_index_permutation(p, n));
        assert(forall|i: int| 0 <= i < n ==> v[i] == v[p[i]]);
    }

    proof fn lemma_swap_permutation(v1: Seq<i32>, v2: Seq<i32>, i: int, j: int)
        requires
            0 <= i < v2.len(),
            0 <= j < v2.len(),
            v1.len() == v2.len(),
            is_permutation(v1, v2),
        ensures
            is_permutation(v1, v2.update(i, v2[j]).update(j, v2[i])),
    {
        let v3 = v2.update(i, v2[j]).update(j, v2[i]);
        let n = v1.len() as int;
        
        let p = choose|p: Seq<int>| is_valid_index_permutation(p, n) 
                && v1.len() == v2.len()
                && (forall|k: int| 0 <= k < n ==> v2[k] == v1[p[k]]);
        
        let p_prime = Seq::new(n as nat, |k: int| 
            if k == i { p[j] }
            else if k == j { p[i] }
            else { p[k] }
        );

        assert(p_prime.len() == n);
        assert forall|x: int, y: int| 0 <= x < y < n implies p_prime[x] != p_prime[y] by {
            if x == i { if y == j {} } else if x == j {}
        };
        assert(is_valid_index_permutation(p_prime, n));
        assert forall|k: int| 0 <= k < n implies v3[k] == v1[p_prime[k]] by {
            if k == i {} else if k == j {} else {}
        };
    }

    proof fn lemma_stitch_sorted(v: Seq<i32>, j: int, end: int)
        requires
            0 <= j < end <= v.len(),
            // 0..j is sorted
            sorted_range(v, 0, j),
            // j+1..end is sorted
            sorted_range(v, j + 1, end),
            // pivot j is smaller than right side
            forall|b: int| j < b < end ==> v[j] <= v[b],
            // left side is smaller than right side
            forall|a: int, b: int| 0 <= a < j && j < b < end ==> v[a] <= v[b],
            // pivot j is larger than left side (stop condition)
            j > 0 ==> v[j-1] <= v[j],
        ensures
            sorted_range(v, 0, end)
    {
        assert forall|a: int, b: int| 0 <= a < b < end implies v[a] <= v[b] by {
            if a < j {
                if b < j {
                    // sorted_range(0, j)
                } else if b == j {
                    // v[a] <= v[j-1] <= v[j]
                    // If a = j-1, trivial. If a < j-1, v[a] <= v[j-1] from sorted(0,j)
                } else {
                    // b > j. v[a] <= v[b] from left-right assumption
                }
            } else if a == j {
                if b > j {
                    // v[j] <= v[b] from pivot assumption
                }
            } else {
                // a > j. sorted_range(j+1, end).
                // Note: a > j implies a >= j+1.
            }
        };
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
        proof { lemma_permutation_refl(v@); }
        if n == 0 { return; }

        for i in 1..n
            invariant
                n == v.len(),
                0 <= i <= n,
                sorted_range(v@, 0, i as int),
                is_permutation(old(v)@, v@),
        {
            let mut j = i;
            
            while j > 0 && v[j-1] > v[j]
                invariant
                    n == v.len(),
                    0 <= j <= i < n,
                    is_permutation(old(v)@, v@),
                    // Prefix
                    sorted_range(v@, 0, j as int),
                    // Suffix (from j+1 to i+1)
                    sorted_range(v@, j as int + 1, i as int + 1),
                    // Pivot vs Suffix
                    (forall|b: int| (j as int) < b && b <= (i as int) ==> v@[j as int] <= v@[b]),
                    // Prefix vs Suffix
                    (forall|a: int, b: int| 0 <= a && a < (j as int) && (j as int) < b && b <= (i as int) ==> v@[a] <= v@[b]),
            {
                let ghost v_prev = v@;
                
                let temp = v[j];
                v.set(j, v[j-1]);
                v.set(j-1, temp);
                
                proof {
                    lemma_swap_permutation(old(v)@, v_prev, (j-1) as int, j as int);
                }
                
                j = j - 1;
            }
            
            proof {
                lemma_stitch_sorted(v@, j as int, i as int + 1);
            }
        }
        proof {
            lemma_sorted_range_to_is_sorted(v@, 0, n as int);
        }
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