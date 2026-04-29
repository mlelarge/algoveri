#include <stdint.h>

/*@
  // Verus: spec fn total_loot(houses: Seq<int>, nums: Seq<int>) -> int
  //   decreases houses.len()
  //   houses.len() == 0 ==> 0
  //   else (if 0 <= houses[0] < nums.len() { nums[houses[0]] } else { 0 })
  //        + total_loot(tail houses, nums)
  // C: houses is an array of indices of length hlen, nums is an array of length nums_len.
  axiomatic HouseRobberSum {
    logic integer total_loot{L}(int *houses, integer k, integer hlen,
                                uint64_t *nums, integer nums_len)
      reads houses[0 .. hlen - 1], nums[0 .. nums_len - 1];

    axiom total_loot_base{L}:
      \forall int *houses, integer hlen, uint64_t *nums, integer nums_len;
        total_loot(houses, hlen, hlen, nums, nums_len) == 0;

    axiom total_loot_step{L}:
      \forall int *houses, integer k, integer hlen,
              uint64_t *nums, integer nums_len;
        0 <= k < hlen ==>
        total_loot(houses, k, hlen, nums, nums_len) ==
          (0 <= houses[k] < nums_len ? (integer) nums[houses[k]] : 0)
          + total_loot(houses, k + 1, hlen, nums, nums_len);
  }

  // Verus: spec fn is_valid_robbery(houses: Seq<int>, nums_len: int) -> bool
  //   forall i. 0 <= i < houses.len() ==> 0 <= houses[i] < nums_len
  //   forall i. 0 <= i < houses.len() - 1 ==> houses[i+1] >= houses[i] + 2
  predicate is_valid_robbery{L}(int *houses, integer hlen, integer nums_len) =
    (hlen == 0 || \valid_read(houses + (0 .. hlen - 1))) &&
    (\forall integer i; 0 <= i < hlen ==> 0 <= houses[i] < nums_len) &&
    (\forall integer i; 0 <= i < hlen - 1 ==> houses[i + 1] >= houses[i] + 2);
*/


/*@
  // Verus: fn rob(nums: &Vec<u64>) -> (max_amount: u64)
  //   Upper bound + Existence over all valid robberies.
  requires 0 <= n <= 100;
  requires \valid_read(nums + (0 .. n - 1));
  requires \forall integer i; 0 <= i < n ==> nums[i] <= 10000;
  assigns \nothing;
  // Upper bound: every valid robbery yields loot <= \result.
  ensures \forall int *houses, integer hlen;
    hlen >= 0 && is_valid_robbery(houses, hlen, n)
    ==> total_loot(houses, 0, hlen, (uint64_t *)nums, n) <= \result;
  // Existence: some valid robbery achieves \result.
  ensures \exists int *houses, integer hlen;
    hlen >= 0 && is_valid_robbery(houses, hlen, n)
    && total_loot(houses, 0, hlen, (uint64_t *)nums, n) == \result;
*/
uint64_t rob(const uint64_t *nums, int n) {
  // Implement and verify rob here.
}
