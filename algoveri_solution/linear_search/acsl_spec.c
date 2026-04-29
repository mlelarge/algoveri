#include <stdint.h>
#include <stddef.h>
#include <limits.h>

/*@
  // Verus: spec fn is_sorted(seq: Seq<i32>) -> bool
  predicate is_sorted{L}(int32_t *seq, integer n) =
    \forall integer i, j; 0 <= i <= j < n ==> seq[i] <= seq[j];
*/

/*@
  requires 0 <= n <= 0x7FFFFFFF;
  requires n == 0 || \valid_read(seq + (0 .. n - 1));
  requires is_sorted((int32_t *)seq, n);
  assigns \nothing;
  ensures 0 <= \result <= n;
  ensures \forall integer i; 0 <= i < \result ==> seq[i] < target;
  ensures \forall integer i; \result <= i < n ==> seq[i] >= target;
*/
size_t linear_search_lower_bound(const int32_t *seq, size_t n, int32_t target) {
  // Implement and verify linear_search_lower_bound here.
}
