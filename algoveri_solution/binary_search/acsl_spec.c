#include <stddef.h>
#include <stdint.h>

/*@
  predicate is_sorted{L}(int32_t *a, integer n) =
    \forall integer i, j; 0 <= i <= j < n ==> a[i] <= a[j];
*/

/*@
  // Verus: fn binary_search_lower_bound(seq: &Vec<i32>, target: i32) -> (result: usize)
  requires 0 <= n <= 0x7FFFFFFF;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  requires is_sorted((int32_t *)a, n);
  assigns \nothing;
  ensures 0 <= \result <= n;
  ensures \forall integer i; 0 <= i < \result ==> a[i] < target;
  ensures \forall integer i; \result <= i < n ==> a[i] >= target;
*/
size_t binary_search_lower_bound(const int32_t *a, size_t n, int32_t target) {
  // Implement and verify binary_search_lower_bound here.
}
