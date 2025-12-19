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
    // </helpers>

    // Following is the block for proofs of lemmas, or functions that help the implementation or verification of the main specification
    // <proofs>
    proof fn lemma_perm_refl(s: Seq<i32>)
        ensures is_permutation(s, s)
    {
        let n = s.len() as int;
        let p = Seq::new(n as nat, |i: int| i);
        assert(is_valid_index_permutation(p, n));
        assert(forall|i: int| 0 <= i < n ==> s[i] == s[#[trigger] p[i]]);
        assert(is_permutation(s, s));
    }

    proof fn lemma_perm_trans(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>)
        requires is_permutation(s1, s2), is_permutation(s2, s3)
        ensures is_permutation(s1, s3)
    {
        let p12 = choose|p12: Seq<int>| is_valid_index_permutation(p12, s1.len() as int) && (forall|i: int| 0 <= i < s1.len() ==> s2[i] == s1[#[trigger] p12[i]]);
        let p23 = choose|p23: Seq<int>| is_valid_index_permutation(p23, s2.len() as int) && (forall|i: int| 0 <= i < s2.len() ==> s3[i] == s2[#[trigger] p23[i]]);
        let n = s1.len() as int;
        let p13 = Seq::new(n as nat, |i: int| p12[p23[i]]);
        
        assert(is_valid_index_permutation(p13, n)) by {
            assert(forall|i: int| 0 <= i < n ==> 0 <= #[trigger] p13[i] < n);
            assert(forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] p13[i] != #[trigger] p13[j]);
        }
        assert(forall|i: int| 0 <= i < n ==> s3[i] == s1[#[trigger] p13[i]]);
        assert(is_permutation(s1, s3));
    }

    proof fn lemma_perm_concat(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>, s4: Seq<i32>)
        requires is_permutation(s1, s2), is_permutation(s3, s4)
        ensures is_permutation(s1.add(s3), s2.add(s4))
    {
        let p12 = choose|p12: Seq<int>| is_valid_index_permutation(p12, s1.len() as int) && (forall|i: int| 0 <= i < s1.len() ==> s2[i] == s1[#[trigger] p12[i]]);
        let p34 = choose|p34: Seq<int>| is_valid_index_permutation(p34, s3.len() as int) && (forall|i: int| 0 <= i < s3.len() ==> s4[i] == s3[#[trigger] p34[i]]);
        let n1 = s1.len() as int;
        let n2 = s3.len() as int;
        let n = n1 + n2;
        let p = Seq::new(n as nat, |i: int| if i < n1 { p12[i] } else { p34[i - n1] + n1 });

        assert(is_valid_index_permutation(p, n)) by {
            assert(forall|i: int| 0 <= i < n ==> 0 <= #[trigger] p[i] < n);
            assert(forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] p[i] != #[trigger] p[j]);
        }
        assert(forall|i: int| 0 <= i < n ==> (s2.add(s4))[i] == (s1.add(s3))[#[trigger] p[i]]) by {
            assert(forall|i: int| 0 <= i < n1 ==> s2[i] == s1[p12[i]]);
            assert(forall|i: int| 0 <= i < n2 ==> s4[i] == s3[p34[i]]);
        }
        assert(is_permutation(s1.add(s3), s2.add(s4)));
    }

    proof fn lemma_perm_swap(s1: Seq<i32>, s2: Seq<i32>)
        ensures is_permutation(s1.add(s2), s2.add(s1))
    {
        let n1 = s1.len() as int;
        let n2 = s2.len() as int;
        let n = n1 + n2;
        let p = Seq::new(n as nat, |i: int| if i < n2 { i + n1 } else { i - n2 });
        assert(is_valid_index_permutation(p, n)) by {
            assert(forall|i: int| 0 <= i < n ==> 0 <= #[trigger] p[i] < n);
            assert(forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] p[i] != #[trigger] p[j]);
        }
        assert(forall|i: int| 0 <= i < n ==> (s2.add(s1))[i] == (s1.add(s2))[#[trigger] p[i]]);
        assert(is_permutation(s1.add(s2), s2.add(s1)));
    }

    fn merge(left: Vec<i32>, right: Vec<i32>) -> (res: Vec<i32>)
        requires
            is_sorted(left@),
            is_sorted(right@),
        ensures
            is_sorted(res@),
            is_permutation(left@.add(right@), res@),
    {
        let mut i: usize = 0;
        let mut j: usize = 0;
        let mut res = Vec::new();
        let ghost n = left.len() as int;
        let ghost m = right.len() as int;
        let ghost orig_seq = left@.add(right@);

        proof { lemma_perm_refl(orig_seq); }

        while i < left.len() || j < right.len()
            invariant
                0 <= i <= n,
                0 <= j <= m,
                is_sorted(res@),
                is_permutation(orig_seq, res@.add(left@.subrange(i as int, n)).add(right@.subrange(j as int, m))),
                forall|k: int| 0 <= k < res.len() ==> (i < n ==> res[k] <= left@[i as int]),
                forall|k: int| 0 <= k < res.len() ==> (j < m ==> res[k] <= right@[j as int]),
        {
            let ghost prev_combined = res@.add(left@.subrange(i as int, n)).add(right@.subrange(j as int, m));
            if i < left.len() && (j == right.len() || left[i] <= right[j]) {
                let val = left[i];
                proof {
                    assert(is_sorted(res@.push(val))) by {
                        assert(forall|k: int| 0 <= k < res.len() ==> res[k] <= val);
                    }
                    if i + 1 < n {
                        assert(left@[i as int] <= left@[i as int + 1]);
                    }
                }
                res.push(val);
                i += 1;
                // res_new + left_sub_new + right_sub == res_old + left_sub_old + right_sub
            } else {
                let val = right[j];
                let ghost val_seq = Seq::empty().push(val);
                let ghost left_sub = left@.subrange(i as int, n);
                let ghost right_sub_new = right@.subrange(j as int + 1, m);
                let ghost next_combined = (res@.push(val)).add(left_sub).add(right_sub_new);

                proof {
                    lemma_perm_swap(left_sub, val_seq); 
                    lemma_perm_refl(res@);
                    lemma_perm_concat(res@, res@, left_sub.add(val_seq), val_seq.add(left_sub));
                    let res_left_y_perm = res@.add(left_sub.add(val_seq));
                    let res_y_left_perm = res@.add(val_seq.add(left_sub));
                    lemma_perm_refl(right_sub_new);
                    lemma_perm_concat(res_left_y_perm, res_y_left_perm, right_sub_new, right_sub_new);
                    lemma_perm_trans(orig_seq, prev_combined, next_combined);

                    assert(is_sorted(res@.push(val))) by {
                        assert(forall|k: int| 0 <= k < res.len() ==> res[k] <= val);
                    }
                    if j + 1 < m {
                        assert(right@[j as int] <= right@[j as int + 1]);
                    }
                }
                res.push(val);
                j += 1;
            }
        }
        proof {
            assert(left@.subrange(i as int, n) == Seq::<i32>::empty());
            assert(right@.subrange(j as int, m) == Seq::<i32>::empty());
        }
        res
    }
    // </proofs>

    // Following is the block for the main specification
    // <spec>
    fn merge_sort(v: &mut Vec<i32>)
        ensures
            is_sorted(v@),
            is_permutation(old(v)@, v@),
    // </spec>
    // <code>
    {
        let n = v.len();
        if n <= 1 {
            proof {
                lemma_perm_refl(v@);
            }
            return;
        }

        let ghost old_v = v@;
        let mid = n / 2;

        let mut left = Vec::new();
        let mut i: usize = 0;
        while i < mid
            invariant
                i <= mid,
                mid <= n,
                left@ == old_v.subrange(0, i as int),
        {
            left.push(v[i]);
            i += 1;
        }

        let mut right = Vec::new();
        while i < n
            invariant
                mid <= i <= n,
                left@ == old_v.subrange(0, mid as int),
                right@ == old_v.subrange(mid as int, i as int),
        {
            right.push(v[i]);
            i += 1;
        }

        let ghost left_orig = left@;
        let ghost right_orig = right@;
        
        merge_sort(&mut left);
        merge_sort(&mut right);

        proof {
            lemma_perm_concat(left_orig, left@, right_orig, right@);
            assert(old_v == left_orig.add(right_orig));
        }
        
        let res = merge(left, right);
        proof {
            lemma_perm_trans(old_v, left@.add(right@), res@);
        }
        *v = res;
    }
    // </code>

    #[verifier::external]
    fn main() {
        let mut v = vec![5, 1, 4, 2, 8];
        merge_sort(&mut v);
        println!("{:?}", v);
    }
}