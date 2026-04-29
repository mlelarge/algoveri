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
  predicate same_multiset{L1,L2}(int32_t *a, integer n) =
    \forall integer v; count_occ{L1}(a, n, v) == count_occ{L2}(a, n, v);
*/


/*@
  requires 0 <= n <= 1000;
  requires n == 0 || \valid(a + (0 .. n - 1));
  assigns a[0 .. n - 1];
  ensures is_sorted(a, n);
  ensures same_multiset{Pre,Post}(a, n);
*/
void quick_sort(int32_t *a, size_t n) {
  // Implement and verify quick_sort here.
}
