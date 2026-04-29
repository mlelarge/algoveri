#include <stdint.h>
#include <stddef.h>

/*@
  // Verus: spec fn spec_sum(seq, start, end) -- recursive sum of seq[start..end)
  // using mathematical integers.
  logic integer spec_sum{L}(int32_t *a, integer start, integer end) =
    (start >= end) ? 0 : a[end - 1] + spec_sum(a, start, end - 1);
*/


/*@
  requires 0 < n <= 100000;
  requires \valid_read(a + (0 .. n - 1));
  assigns \nothing;
  ensures \forall integer i, j; 0 <= i <= j <= n ==> spec_sum((int32_t *)a, i, j) <= \result;
  ensures \exists integer i, j; 0 <= i <= j <= n && spec_sum((int32_t *)a, i, j) == \result;
*/
int64_t max_subarray_sum(const int32_t *a, size_t n) {
  // Implement and verify max_subarray_sum here.
}
