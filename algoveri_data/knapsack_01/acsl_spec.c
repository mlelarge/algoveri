#include <stdint.h>

/*@
  // Verus: spec fn total_weight(selected: Seq<bool>, weights: Seq<int>) -> int
  //   decreases selected.len()
  //   selected.len() == 0 ==> 0
  //   else (if selected[0] { weights[0] } else { 0 })
  //        + total_weight(tail selected, tail weights)
  // C: selected and weights are arrays of length n; recurse on 0-based index k.
  axiomatic Knapsack01Sums {
    logic integer total_weight{L}(int *selected, uint64_t *weights, integer k, integer n)
      reads selected[0 .. n - 1], weights[0 .. n - 1];

    axiom total_weight_base{L}:
      \forall int *selected, uint64_t *weights, integer n;
        total_weight(selected, weights, n, n) == 0;

    axiom total_weight_step{L}:
      \forall int *selected, uint64_t *weights, integer k, integer n;
        0 <= k < n ==>
        total_weight(selected, weights, k, n) ==
          (selected[k] != 0 ? (integer) weights[k] : 0)
          + total_weight(selected, weights, k + 1, n);

    // Verus: spec fn total_value(selected: Seq<bool>, values: Seq<int>) -> int
    logic integer total_value{L}(int *selected, uint64_t *values, integer k, integer n)
      reads selected[0 .. n - 1], values[0 .. n - 1];

    axiom total_value_base{L}:
      \forall int *selected, uint64_t *values, integer n;
        total_value(selected, values, n, n) == 0;

    axiom total_value_step{L}:
      \forall int *selected, uint64_t *values, integer k, integer n;
        0 <= k < n ==>
        total_value(selected, values, k, n) ==
          (selected[k] != 0 ? (integer) values[k] : 0)
          + total_value(selected, values, k + 1, n);
  }

  // Verus: spec fn is_valid_strategy(selected, weights, capacity) -> bool
  //   selected.len() == weights.len() && total_weight(selected, weights) <= capacity
  predicate is_valid_strategy{L}(int *selected, uint64_t *weights,
                                  integer n, integer capacity) =
    \valid_read(selected + (0 .. n - 1)) &&
    \valid_read(weights + (0 .. n - 1)) &&
    (\forall integer i; 0 <= i < n ==> (selected[i] == 0 || selected[i] == 1)) &&
    total_weight(selected, weights, 0, n) <= capacity;
*/


/*@
  // Verus: fn solve_knapsack_01(weights: &Vec<u64>, values: &Vec<u64>, capacity: u64)
  //          -> (max_val: u64)
  //   Upper bound + Existence over all valid_strategy selections.
  requires 0 <= n <= 100;
  requires capacity <= 1000;
  requires \valid_read(weights + (0 .. n - 1));
  requires \valid_read(values  + (0 .. n - 1));
  requires \forall integer i; 0 <= i < n ==> weights[i] <= 1000;
  requires \forall integer i; 0 <= i < n ==> values[i]  <= 1000;
  assigns \nothing;
  // Upper bound: every valid strategy yields value <= \result.
  ensures \forall int *selected;
    is_valid_strategy(selected, (uint64_t *)weights, n, capacity)
    ==> total_value(selected, (uint64_t *)values, 0, n) <= \result;
  // Existence: some valid strategy achieves \result.
  ensures \exists int *selected;
    is_valid_strategy(selected, (uint64_t *)weights, n, capacity)
    && total_value(selected, (uint64_t *)values, 0, n) == \result;
*/
uint64_t solve_knapsack_01(const uint64_t *weights, const uint64_t *values,
                           int n, uint64_t capacity) {
  // Implement and verify solve_knapsack_01 here.
}
