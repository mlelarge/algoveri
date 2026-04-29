#include <stddef.h>
#include <stdint.h>

/*@
  predicate valid_nums{L}(uint64_t *nums, integer n) =
    0 < n <= 10000 &&
    \valid_read(nums + (0 .. n - 1)) &&
    (\forall integer i; 0 <= i < n ==> nums[i] <= 10000);

  // Verus: spec fn is_valid_jump_path(path: Seq<int>, nums: Seq<int>) -> bool
  // path[0] == 0; path.last() == n - 1; strictly forward jumps bounded by
  // nums[path[i]].
  predicate is_valid_jump_path{L}(int *path, integer plen,
                                   uint64_t *nums, integer n) =
    plen >= 1 &&
    \valid_read(path + (0 .. plen - 1)) &&
    path[0] == 0 &&
    path[plen - 1] == n - 1 &&
    (\forall integer i; 0 <= i < plen ==> 0 <= path[i] < n) &&
    (\forall integer i; 0 <= i < plen - 1 ==>
       path[i + 1] > path[i] &&
       path[i + 1] <= path[i] + nums[path[i]]);

  // Verus: reachable <==> exists path. is_valid_jump_path(path, nums)
  predicate can_reach{L}(uint64_t *nums, integer n) =
    \exists int *path, integer plen;
      is_valid_jump_path(path, plen, nums, n);
*/

/*@
  // Verus: fn can_jump(nums: &Vec<u64>) -> (reachable: bool)
  requires valid_nums((uint64_t *)nums, n);
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> can_reach((uint64_t *)nums, n);
*/
int can_jump(const uint64_t *nums, size_t n) {
  // Implement and verify can_jump here.
}
