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
        let n = s.len();
        let p = Seq::new(n as nat, |i: int| i);
        assert(is_valid_index_permutation(p, n as int));
        assert(forall|i: int| 0 <= i < n ==> s[i] == s[#[trigger] p[i]]);
        assert(is_permutation(s, s));
    }

    proof fn lemma_perm_trans(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>)
        requires is_permutation(s1, s2), is_permutation(s2, s3)
        ensures is_permutation(s1, s3)
    {
        let p12 = choose|p12: Seq<int>| is_valid_index_permutation(p12, s1.len() as int) && (forall|i: int| 0 <= i < s1.len() ==> s2[i] == s1[#[trigger] p12[i]]);
        let p23 = choose|p23: Seq<int>| is_valid_index_permutation(p23, s2.len() as int) && (forall|i: int| 0 <= i < s2.len() ==> s3[i] == s2[#[trigger] p23[i]]);
        let n = s1.len();
        let p13 = Seq::new(n as nat, |i: int| p12[p23[i]]);
        
        assert(is_valid_index_permutation(p13, n as int)) by {
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
        let n1 = s1.len();
        let n2 = s3.len();
        let n = n1 + n2;
        let p = Seq::new(n as nat, |i: int| if i < n1 { p12[i] } else { p34[i - n1] + n1 });

        assert(is_valid_index_permutation(p, n as int)) by {
            assert(forall|i: int| 0 <= i < n ==> 0 <= #[trigger] p[i] < n);
            assert(forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] p[i] != #[trigger] p[j]);
        }
        assert(forall|i: int| 0 <= i < n ==> (s2.add(s4))[i] == (s1.add(s3))[#[trigger] p[i]]);
        assert(is_permutation(s1.add(s3), s2.add(s4)));
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
        let ghost orig_seq = left@.add(right@);
        let n = left.len() as int;
        let m = right.len() as int;

        lemma_perm_refl(orig_seq);

        while i < left.len() || j < right.len()
            invariant
                0 <= i <= n,
                0 <= j <= m,
                is_sorted(res@),
                is_permutation(orig_seq, res@.add(left@.subrange(i as int, n)).add(right@.subrange(j as int, m))),
                forall|k: int| 0 <= k < res.len() ==> (i < n ==> res[k] <= #[trigger] left[i as int]),
                forall|k: int| 0 <= k < res.len() ==> (j < m ==> res[k] <= #[trigger] right[j as int]),
        {
            let ghost prev_combined = res@.add(left@.subrange(i as int, n)).add(right@.subrange(j as int, m));
            let ghost prev_res = res@;
            if i < left.len() && (j == right.len() || left[i] <= right[j]) {
                assert(left@.subrange(i as int, n) == Seq::empty().push(left[i as int]).add(left@.subrange(i as int + 1, n)));
                res.push(left[i]);
                i += 1;
                assert(res@.add(left@.subrange(i as int, n)).add(right@.subrange(j as int, m)) == prev_combined);
            } else {
                assert(right@.subrange(j as int, m) == Seq::empty().push(right[j as int]).add(right@.subrange(j as int + 1, m)));
                res.push(right[j]);
                j += 1;
                assert(res@.add(left@.subrange(i as int, n)).add(right@.subrange(j as int, m)) == prev_combined);
            }
        }
        assert(left@.subrange(i as int, n) == Seq::<i32>::empty());
        assert(right@.subrange(j as int, m) == Seq::<i32>::empty());
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
            lemma_perm_refl(v@);
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

        assert(old_v == left@.add(right@));
        let ghost left_orig = left@;
        let ghost right_orig = right@;
        
        merge_sort(&mut left);
        merge_sort(&mut right);

        lemma_perm_concat(left_orig, left@, right_orig, right@);
        // This establishes is_permutation(old_v, left@.add(right@))
        
        let res = merge(left, right);
        // merge ensures is_permutation(left_sorted.add(right_sorted), res@)
        lemma_perm_trans(old_v, left@.add(right@), res@);
        
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