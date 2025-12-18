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

    // <helpers>
    // </helpers>

    // <proofs>
    proof fn lemma_perm_refl(s: Seq<i32>)
        ensures is_permutation(s, s)
    {
        let p = Seq::new(s.len(), |i: int| i);
        assert(is_valid_index_permutation(p, s.len() as int));
        assert(forall|i: int| 0 <= i < s.len() ==> s[i] == s[p[i]]);
    }

    proof fn lemma_perm_trans(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>)
        requires is_permutation(s1, s2), is_permutation(s2, s3)
        ensures is_permutation(s1, s3)
    {
        let p1 = choose|p: Seq<int>| is_valid_index_permutation(p, s1.len() as int) && s1.len() == s2.len() && (forall|i: int| 0 <= i < s1.len() ==> s2[i] == s1[p[i]]);
        let p2 = choose|p: Seq<int>| is_valid_index_permutation(p, s2.len() as int) && s2.len() == s3.len() && (forall|i: int| 0 <= i < s2.len() ==> s3[i] == s2[p[i]]);
        
        let p3 = Seq::new(s3.len(), |i: int| p1[p2[i]]);
        
        assert(p3.len() == s3.len());
        
        // Validity of p3
        assert(forall|i: int| 0 <= i < s3.len() ==> 0 <= p3[i] < s1.len());

        // Injectivity of p3
        // p2 is injective, p1 is injective. p3 = p1 o p2.
        assert(forall|i: int, j: int| 0 <= i < j < s3.len() ==> p3[i] != p3[j]) by {
            if p3[i] == p3[j] {
                // p1[p2[i]] == p1[p2[j]] => p2[i] == p2[j] => i == j
            }
        }
        
        assert(is_valid_index_permutation(p3, s1.len() as int));
        assert(forall|i: int| 0 <= i < s3.len() ==> s3[i] == s1[p3[i]]);
    }

    proof fn lemma_perm_append(s1: Seq<i32>, s2: Seq<i32>, x: i32)
        requires is_permutation(s1, s2)
        ensures is_permutation(s1.push(x), s2.push(x))
    {
        let p = choose|p: Seq<int>| is_valid_index_permutation(p, s1.len() as int) && s1.len() == s2.len() && (forall|i: int| 0 <= i < s1.len() ==> s2[i] == s1[p[i]]);
        let n = s1.len();
        let p_new = Seq::new(n + 1, |i: int| if i < n { p[i] } else { n as int });
        
        assert(forall|i: int| 0 <= i < n + 1 ==> 0 <= p_new[i] < n + 1);
        assert(forall|i: int, j: int| 0 <= i < j < n + 1 ==> p_new[i] != p_new[j]);
        
        assert(is_valid_index_permutation(p_new, (n + 1) as int));
        assert(forall|i: int| 0 <= i < n + 1 ==> s2.push(x)[i] == s1.push(x)[p_new[i]]);
    }

    // Proves is_permutation((a+x)+b, (a+b)+x)
    proof fn lemma_perm_move_element(a: Seq<i32>, b: Seq<i32>, x: i32)
        ensures is_permutation((a.push(x)) + b, (a + b).push(x))
    {
        let s1 = (a.push(x)) + b;
        let s2 = (a + b).push(x);
        let n_a = a.len() as int;
        let n_b = b.len() as int;
        let n = n_a + n_b + 1;
        
        // p maps indices of s2 (target) to indices of s1 (source)
        let p = Seq::new(n as nat, |i: int| 
            if i < n_a { i } 
            else if i < n_a + n_b { i + 1 } 
            else { n_a }
        );
        
        let inv_p = Seq::new(n as nat, |j: int|
            if j < n_a { j }
            else if j == n_a { n_a + n_b }
            else { j - 1 }
        );
        
        assert(forall|i: int| 0 <= i < n ==> 0 <= p[i] < n);
        assert(forall|i: int| 0 <= i < n ==> inv_p[p[i]] == i);
        
        assert(forall|i: int, j: int| 0 <= i < j < n ==> p[i] != p[j]) by {
            if p[i] == p[j] {
                // inv_p[p[i]] == inv_p[p[j]] => i == j
            }
        }
        
        assert(is_valid_index_permutation(p, n));
        assert(forall|i: int| 0 <= i < n ==> s2[i] == s1[p[i]]);
    }

    proof fn lemma_perm_concat(s1: Seq<i32>, s2: Seq<i32>, t1: Seq<i32>, t2: Seq<i32>)
        requires is_permutation(s1, t1), is_permutation(s2, t2)
        ensures is_permutation(s1 + s2, t1 + t2)
    {
        let p1 = choose|p: Seq<int>| is_valid_index_permutation(p, s1.len() as int) && s1.len() == t1.len() && (forall|i: int| 0 <= i < s1.len() ==> t1[i] == s1[p[i]]);
        let p2 = choose|p: Seq<int>| is_valid_index_permutation(p, s2.len() as int) && s2.len() == t2.len() && (forall|i: int| 0 <= i < s2.len() ==> t2[i] == s2[p[i]]);
        
        let n1 = s1.len();
        let n2 = s2.len();
        let p = Seq::new(n1 + n2, |i: int| if i < n1 { p1[i] } else { p2[i - n1] + (n1 as int) });
        
        assert(forall|i: int| 0 <= i < n1 + n2 ==> 0 <= p[i] < n1 + n2);
        assert(forall|i: int, j: int| 0 <= i < j < n1 + n2 ==> p[i] != p[j]);

        assert(is_valid_index_permutation(p, (n1 + n2) as int));
        assert(forall|i: int| 0 <= i < n1 + n2 ==> (t1 + t2)[i] == (s1 + s2)[p[i]]);
    }

    proof fn lemma_sorted_snoc(s: Seq<i32>, x: i32)
        requires is_sorted(s), s.len() > 0 ==> s.last() <= x
        ensures is_sorted(s.push(x))
    {
    }

    proof fn lemma_subrange_extension(s: Seq<i32>, k: int)
        requires 0 <= k < s.len()
        ensures s.subrange(0, k + 1) =~= s.subrange(0, k).push(s[k])
    {
    }

    fn merge(v1: &Vec<i32>, v2: &Vec<i32>) -> (res: Vec<i32>)
        requires is_sorted(v1@), is_sorted(v2@)
        ensures 
            is_sorted(res@),
            is_permutation(v1@ + v2@, res@),
            res@.len() == v1@.len() + v2@.len(),
    {
        let mut res = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        let ghost v1_seq = v1@;
        let ghost v2_seq = v2@;
        let ghost n1 = v1@.len();
        let ghost n2 = v2@.len();

        proof { lemma_perm_refl(Seq::empty()); }

        while i < v1.len() || j < v2.len()
            invariant
                0 <= i <= n1,
                0 <= j <= n2,
                n1 == v1.len(),
                n2 == v2.len(),
                is_sorted(res@),
                res@.len() == i + j,
                is_permutation(v1_seq.subrange(0, i as int) + v2_seq.subrange(0, j as int), res@),
                forall|k| 0 <= k < res.len() ==> (i < n1 ==> res@[k] <= v1@[i as int]),
                forall|k| 0 <= k < res.len() ==> (j < n2 ==> res@[k] <= v2@[j as int]),
            decreases (v1.len() - i) + (v2.len() - j)
        {
            let ghost old_res = res@;
            let ghost consumed = v1_seq.subrange(0, i as int) + v2_seq.subrange(0, j as int);

            if i < v1.len() && (j == v2.len() || v1[i] <= v2[j]) {
                let val = v1[i];
                proof {
                    lemma_sorted_snoc(res@, val);
                    lemma_perm_append(consumed, res@, val);
                    
                    // Show permutation move
                    lemma_subrange_extension(v1_seq, i as int);
                    lemma_perm_move_element(v1_seq.subrange(0, i as int), v2_seq.subrange(0, j as int), val);
                    
                    // Transitivity
                    lemma_perm_trans(v1_seq.subrange(0, (i+1) as int) + v2_seq.subrange(0, j as int), consumed.push(val), res@.push(val));
                }
                res.push(val);
                i += 1;
            } else {
                let val = v2[j];
                proof {
                    lemma_sorted_snoc(res@, val);
                    lemma_perm_append(consumed, res@, val);
                    lemma_subrange_extension(v2_seq, j as int);
                }
                res.push(val);
                j += 1;
            }
        }
        res
    }

    // <spec>
    fn merge_sort(v: &mut Vec<i32>)
        ensures
            is_sorted(v@),
            is_permutation(old(v)@, v@),
        decreases old(v)@.len()
    // </spec>
    // <code>
    {
        let n = v.len();
        if n <= 1 {
            proof { lemma_perm_refl(v@); }
            return;
        }

        let mid = n / 2;
        let mut left = Vec::new();
        let mut right = Vec::new();

        let ghost original_v = v@;
        
        let mut k: usize = 0;
        while k < mid 
            invariant 
                0 <= k <= mid, 
                n == v.len(),
                mid <= n,
                left@ == original_v.subrange(0, k as int),
                v@ == original_v
            decreases mid - k
        {
            let val = v[k];
            left.push(val);
            proof {
                lemma_subrange_extension(original_v, k as int);
            }
            k += 1;
        }

        let mut m: usize = mid;
        while m < n
            invariant 
                mid <= m <= n, 
                n == v.len(),
                right@ == original_v.subrange(mid as int, m as int),
                v@ == original_v
            decreases n - m
        {
            let val = v[m];
            right.push(val);
            proof {
                // right starts empty. right is subrange(mid, m).
                // right.push(val) is subrange(mid, m) + val.
                // We want subrange(mid, m+1).
                // subrange(mid, m+1) = subrange(mid, m) + val.
                // This is a property of subrange and push.
                // Need to match the types.
                // original_v.subrange(mid, m+1) == original_v.subrange(mid, m).push(original_v[m])
                // original_v[m] is v[m].
                assert(original_v.subrange(mid as int, (m + 1) as int) =~= original_v.subrange(mid as int, m as int).push(original_v[m as int]));
            }
            m += 1;
        }

        assert(v@ =~= left@ + right@);

        let ghost old_left = left@;
        let ghost old_right = right@;

        merge_sort(&mut left);
        merge_sort(&mut right);

        proof {
            lemma_perm_concat(old_left, old_right, left@, right@);
        }

        let res = merge(&left, &right);
        
        proof {
            lemma_perm_trans(original_v, left@ + right@, res@);
        }

        *v = res;
    }
    // </code>

    #[verifier::external]
    fn main() {
        let mut v = vec![5, 1, 4, 2, 8];
        let ghost original_v = v@;
        
        merge_sort(&mut v);
        
        assert(is_sorted(v@));
        assert(is_permutation(original_v, v@));
    }
}