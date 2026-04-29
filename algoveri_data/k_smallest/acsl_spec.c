#include <stdint.h>
#include <stddef.h>

/*@
  // Verus: spec fn is_sorted(s: Seq<i32>) -> bool
  predicate is_sorted{L}(int32_t *a, integer n) =
    \forall integer i, j; 0 <= i < j < n ==> a[i] <= a[j];

  // Verus: helper used by is_permutation; counts occurrences of v in a[0..n).
  logic integer count_occ{L}(int32_t *a, integer n, integer v) =
    n <= 0 ? 0 :
    count_occ(a, n - 1, v) + ((a[n - 1] == v) ? 1 : 0);

  // Verus: spec fn is_permutation(v1, v2) (index-permutation form);
  // here expressed as multiset-equality via count_occ.
  predicate is_permutation{L1,L2}(int32_t *a, integer n) =
    \forall integer v; count_occ{L1}(a, n, v) == count_occ{L2}(a, n, v);

  // Verus: spec fn is_kth_smallest(s, k, val) -- val is the k-th smallest
  // element of s, i.e. some sorted permutation of s has val at index k.
  predicate is_kth_smallest{L1,L2}(int32_t *a, integer n, integer k, integer val) =
    0 <= k < n &&
    is_sorted{L2}(a, n) &&
    is_permutation{L1,L2}(a, n) &&
    val == \at(a[k], L2);
*/

/*@
  requires 0 <= n <= 10000;
  requires \valid(a + (0 .. n - 1));
  requires 0 <= k < n;
  assigns a[0 .. n - 1];
  ensures is_permutation{Pre,Post}(a, n);
  ensures is_kth_smallest{Pre,Post}(a, n, k, \result);
*/
int32_t quick_select(int32_t *a, size_t n, size_t k) {
  // Implement and verify quick_select here.
}
