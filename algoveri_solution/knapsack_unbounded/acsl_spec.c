#include <stdint.h>

/*@
  // Verus: spec fn total_weight(counts: Seq<int>, weights: Seq<int>) -> int
  //   decreases counts.len()
  //   counts.len() == 0 ==> 0
  //   else counts[0] * weights[0] + total_weight(tail, tail)
  axiomatic KnapsackUnboundedSums {
    logic integer total_weight{L}(int *counts, uint64_t *weights, integer k, integer n)
      reads counts[0 .. n - 1], weights[0 .. n - 1];

    axiom total_weight_base{L}:
      \forall int *counts, uint64_t *weights, integer n;
        total_weight(counts, weights, n, n) == 0;

    axiom total_weight_step{L}:
      \forall int *counts, uint64_t *weights, integer k, integer n;
        0 <= k < n ==>
        total_weight(counts, weights, k, n) ==
          counts[k] * weights[k] + total_weight(counts, weights, k + 1, n);

    // Verus: spec fn total_value(counts: Seq<int>, values: Seq<int>) -> int
    logic integer total_value{L}(int *counts, uint64_t *values, integer k, integer n)
      reads counts[0 .. n - 1], values[0 .. n - 1];

    axiom total_value_base{L}:
      \forall int *counts, uint64_t *values, integer n;
        total_value(counts, values, n, n) == 0;

    axiom total_value_step{L}:
      \forall int *counts, uint64_t *values, integer k, integer n;
        0 <= k < n ==>
        total_value(counts, values, k, n) ==
          counts[k] * values[k] + total_value(counts, values, k + 1, n);
  }

  // Verus: spec fn is_valid_strategy(counts, weights, capacity) -> bool
  //   counts.len() == weights.len() &&
  //   forall i. 0 <= i < counts.len() ==> counts[i] >= 0 &&
  //   total_weight(counts, weights) <= capacity
  predicate is_valid_strategy{L}(int *counts, uint64_t *weights,
                                  integer n, integer capacity) =
    \valid_read(counts + (0 .. n - 1)) &&
    \valid_read(weights + (0 .. n - 1)) &&
    (\forall integer i; 0 <= i < n ==> counts[i] >= 0) &&
    total_weight(counts, weights, 0, n) <= capacity;
*/


/*@
  // Verus: fn solve_knapsack_unbounded(weights, values, capacity) -> (max_val: u64)
  //   Upper bound + Existence over all valid count vectors.
  requires 0 < n <= 100;
  requires capacity <= 1000;
  requires \valid_read(weights + (0 .. n - 1));
  requires \valid_read(values  + (0 .. n - 1));
  requires \forall integer i; 0 <= i < n ==> 0 < weights[i] <= 1000;
  requires \forall integer i; 0 <= i < n ==> values[i] <= 1000;
  assigns \nothing;
  ensures \forall int *counts;
    is_valid_strategy(counts, (uint64_t *)weights, n, capacity)
    ==> total_value(counts, (uint64_t *)values, 0, n) <= \result;
  ensures \exists int *counts;
    is_valid_strategy(counts, (uint64_t *)weights, n, capacity)
    && total_value(counts, (uint64_t *)values, 0, n) == \result;
*/
uint64_t solve_knapsack_unbounded(const uint64_t *weights, const uint64_t *values,
                                  int n, uint64_t capacity) {
  // Implement and verify solve_knapsack_unbounded here.
}
