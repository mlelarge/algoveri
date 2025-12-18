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
    spec fn is_sorted_range(s: Seq<i32>, low: int, high: int) -> bool {
        forall|i: int, j: int| low <= i < j < high ==> s[i] <= s[j]
    }
    // </helpers>

    // Following is the block for proofs of lemmas, or functions that help the implementation or verification of the main specification
    // <proofs>
    proof fn lemma_perm_reflexive(v: Seq<i32>)
        ensures is_permutation(v, v)
    {
        let n = v.len() as int;
        let p = Seq::new(n as nat, |i: int| i);
        assert(is_valid_index_permutation(p, n));
        assert(forall|i: int| 0 <= i < n ==> v[i] == v[#[trigger] p[i]]);
    }

    proof fn lemma_perm_transitive(v1: Seq<i32>, v2: Seq<i32>, v3: Seq<i32>)
        requires is_permutation(v1, v2), is_permutation(v2, v3)
        ensures is_permutation(v1, v3)
    {
        let p12 = choose|p: Seq<int>| is_valid_index_permutation(p, v1.len() as int) &&
            (forall|i: int| 0 <= i < v1.len() ==> v2[i] == v1[#[trigger] p[i]]);
        let p23 = choose|p: Seq<int>| is_valid_index_permutation(p, v2.len() as int) &&
            (forall|i: int| 0 <= i < v2.len() ==> v3[i] == v2[#[trigger] p[i]]);
        
        let n = v1.len() as int;
        let p13 = Seq::new(n as nat, |i: int| p12[p23[i]]);
        
        forall|i: int, j: int| 0 <= i < j < n ensures #[trigger] p13[i] != #[trigger] p13[j] {
            let pi = p23[i];
            let pj = p23[j];
            if pi < pj {
                assert(p12[pi] != p12[pj]);
            } else {
                assert(p12[pj] != p12[pi]);
            }
        }
        assert(is_valid_index_permutation(p13, n));
        assert(forall|i: int| 0 <= i < n ==> v3[i] == v1[#[trigger] p13[i]]);
        assert exists|p: Seq<int>| is_valid_index_permutation(p, v1.len() as int) 
            && v1.len() == v3.len()
            && (forall|i: int| 0 <= i < v1.len() ==> v3[i] == v1[#[trigger] p[i]]);
    }

    proof fn lemma_perm_swap(v1: Seq<i32>, i: int, j: int)
        requires 0 <= i < v1.len(), 0 <= j < v1.len()
        ensures is_permutation(v1, v1.update(i, v1[j]).update(j, v1[i]))
    {
        let n = v1.len() as int;
        let v2 = v1.update(i, v1[j]).update(j, v1[i]);
        let p = Seq::new(n as nat, |k: int| if k == i { j } else if k == j { i } else { k });
        assert(is_valid_index_permutation(p, n));
        assert(forall|k: int| 0 <= k < n ==> v2[k] == v1[#[trigger] p[k]]);
    }

    proof fn lemma_perm_range(p: Seq<int>, n: int, low: int, high: int)
        requires
            is_valid_index_permutation(p, n),
            forall|k: int| 0 <= k < low ==> p[#[trigger] k] == k,
            forall|k: int| high <= k < n ==> p[#[trigger] k] == k,
        ensures
            forall|k: int| low <= k < high ==> low <= #[trigger] p[k] < high,
    {
        forall|k: int| low <= k < high ensures low <= #[trigger] p[k] < high {
            let pk = p[k];
            if pk < low {
                assert(p[pk] == pk);
            }
            if pk >= high {
                assert(p[pk] == pk);
            }
        }
    }

    proof fn lemma_perm_preserves_bounds(v1: Seq<i32>, v2: Seq<i32>, low: int, high: int, pivot_val: i32, less: bool)
        requires
            is_permutation(v1, v2),
            v1.len() == v2.len(),
            forall|k: int| 0 <= k < low ==> v1[k] == v2[k],
            forall|k: int| high <= k < v1.len() ==> v1[k] == v2[k],
            less ==> (forall|k: int| low <= k < high ==> v1[k] < pivot_val),
            !less ==> (forall|k: int| low <= k < high ==> v1[k] >= pivot_val),
        ensures
            less ==> (forall|k: int| low <= k < high ==> v2[k] < pivot_val),
            !less ==> (forall|k: int| low <= k < high ==> v2[k] >= pivot_val),
    {
        let p = choose|p: Seq<int>| is_valid_index_permutation(p, v1.len() as int) &&
            (forall|i: int| 0 <= i < v1.len() ==> v2[i] == v1[#[trigger] p[i]]);
        lemma_perm_range(p, v1.len() as int, low, high);
        forall|k: int| low <= k < high ensures (less ==> v2[k] < pivot_val) && (!less ==> v2[k] >= pivot_val) {
            let pk = p[k];
            assert(v2[k] == v1[pk]);
        }
    }

    proof fn lemma_sorted_range_merge(v: Seq<i32>, low: int, pivot: int, high: int)
        requires
            is_sorted_range(v, low, pivot),
            is_sorted_range(v, pivot + 1, high),
            forall|k: int| low <= k < pivot ==> v[k] < v[pivot],
            forall|k: int| pivot < k < high ==> v[k] >= v[pivot],
        ensures
            is_sorted_range(v, low, high),
    {
        forall|i: int, j: int| low <= i < j < high ensures v[i] <= v[j] {
            if i < pivot && j == pivot { }
            else if i == pivot && j > pivot { }
            else if i < pivot && j > pivot {
                assert(v[i] < v[pivot]);
                assert(v[pivot] <= v[j]);
            }
        }
    }

    fn partition(v: &mut Vec<i32>, low: usize, high: usize) -> (pivot_idx: usize)
        requires 0 <= low < high <= v.len(),
        ensures
            low <= pivot_idx < high,
            v[pivot_idx as int] == (old(v))[low as int],
            forall|k: int| low <= k < pivot_idx ==> v[k] < v[pivot_idx as int],
            forall|k: int| pivot_idx < k < high ==> v[k] >= v[pivot_idx as int],
            forall|k: int| 0 <= k < low ==> v[k] == (old(v))[k],
            forall|k: int| high <= k < v.len() ==> v[k] == (old(v))[k],
            is_permutation(old(v)@, v@),
    {
        let ghost v_start = v@;
        let pivot = v[low];
        let mut i = low;
        
        for j in low + 1..high
            invariant
                low <= i < j <= high,
                v[low as int] == pivot,
                forall|k: int| low + 1 <= k <= i ==> v[k] < pivot,
                forall|k: int| i + 1 <= k < j ==> v[k] >= pivot,
                forall|k: int| 0 <= k < low ==> v[k] == v_start[k],
                forall|k: int| high <= k < v_start.len() ==> v[k] == v_start[k],
                is_permutation(v_start, v@),
        {
            let ghost v_before = v@;
            if v[j] < pivot {
                i += 1;
                v.swap(i, j);
                lemma_perm_swap(v_before, i as int, j as int);
                lemma_perm_transitive(v_start, v_before, v@);
            }
        }
        let ghost v_before_final = v@;
        v.swap(low, i);
        lemma_perm_swap(v_before_final, low as int, i as int);
        lemma_perm_transitive(v_start, v_before_final, v@);
        i
    }

    fn quick_sort_recursive(v: &mut Vec<i32>, low: usize, high: usize)
        requires 0 <= low <= high <= v.len(),
        ensures
            is_sorted_range(v@, low, high),
            is_permutation(old(v)@, v@),
            forall|k: int| 0 <= k < low ==> v[k] == (old(v))[k],
            forall|k: int| high <= k < v.len() ==> v[k] == (old(v))[k],
        decreases high - low,
    {
        if high - low <= 1 {
            lemma_perm_reflexive(v@);
            return;
        }
        let ghost v0 = v@;
        let pivot_idx = partition(v, low, high);
        let pivot_val = v[pivot_idx as int];
        let ghost v1 = v@;

        quick_sort_recursive(v, low, pivot_idx);
        let ghost v2 = v@;
        lemma_perm_transitive(v0, v1, v2);
        lemma_perm_preserves_bounds(v1, v2, low as int, pivot_idx as int, pivot_val, true);
        
        quick_sort_recursive(v, pivot_idx + 1, high);
        let ghost v3 = v@;
        lemma_perm_transitive(v0, v2, v3);
        lemma_perm_preserves_bounds(v2, v3, (pivot_idx + 1) as int, high as int, pivot_val, false);
        
        lemma_sorted_range_merge(v@, low as int, pivot_idx as int, high as int);
    }
    // </proofs>

    // Following is the block for the main specification
    // <spec>
    fn quick_sort(v: &mut Vec<i32>)
        ensures
            is_sorted(v@),
            is_permutation(old(v)@, v@),
    // </spec>
    // <code>
    {
        let n = v.len();
        quick_sort_recursive(v, 0, n);
    }
    // </code>

    #[verifier::external]
    fn main() {
        let mut v = vec![5, 1, 4, 2, 8];
        let ghost original_v = v@;
        
        quick_sort(&mut v);
        
        assert(is_sorted(v@));
        assert(is_permutation(original_v, v@));
        println!("{:?}", v);
    }
}