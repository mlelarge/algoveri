#include <stdint.h>

/*@
  // Verus: spec fn total_amount(counts: Seq<int>, coins: Seq<int>) -> int
  //   decreases counts.len()
  //   counts.len() == 0 ==> 0
  //   else counts[0] * coins[0] + total_amount(tail counts, tail coins)
  // C: counts and coins are arrays of length n; we recurse on a 0-based index k
  // running from 0 up to n.
  axiomatic CoinChangeSums {
    logic integer total_amount{L}(int *counts, uint64_t *coins, integer k, integer n)
      reads counts[0 .. n - 1], coins[0 .. n - 1];

    axiom total_amount_base{L}:
      \forall int *counts, uint64_t *coins, integer n;
        total_amount(counts, coins, n, n) == 0;

    axiom total_amount_step{L}:
      \forall int *counts, uint64_t *coins, integer k, integer n;
        0 <= k < n ==>
        total_amount(counts, coins, k, n) ==
          counts[k] * coins[k] + total_amount(counts, coins, k + 1, n);

    // Verus: spec fn total_coins(counts: Seq<int>) -> int
    logic integer total_coins{L}(int *counts, integer k, integer n)
      reads counts[0 .. n - 1];

    axiom total_coins_base{L}:
      \forall int *counts, integer n;
        total_coins(counts, n, n) == 0;

    axiom total_coins_step{L}:
      \forall int *counts, integer k, integer n;
        0 <= k < n ==>
        total_coins(counts, k, n) ==
          counts[k] + total_coins(counts, k + 1, n);
  }

  // Verus: spec fn is_valid_change(counts, coins, amount) -> bool
  //   counts.len() == coins.len()
  //   && forall i. 0 <= i < counts.len() ==> counts[i] >= 0
  //   && total_amount(counts, coins) == amount
  // C: counts and coins both have length n.
  predicate is_valid_change{L}(int *counts, uint64_t *coins, integer n, integer amount) =
    \valid_read(counts + (0 .. n - 1)) &&
    \valid_read(coins + (0 .. n - 1)) &&
    (\forall integer i; 0 <= i < n ==> counts[i] >= 0) &&
    total_amount(counts, coins, 0, n) == amount;
*/


/*@
  // Verus: fn coin_change(coins: &Vec<u64>, amount: u64) -> (min_coins: i64)
  //   Returns -1 if impossible, otherwise the minimum total number of coins
  //   over all valid_change strategies.
  requires 0 < n <= 100;
  requires amount <= 10000;
  requires \valid_read(coins + (0 .. n - 1));
  requires \forall integer i; 0 <= i < n ==> 0 < coins[i] <= 10000;
  assigns \nothing;
  // Case 1: a solution exists.
  ensures \result != -1 ==>
    (\exists int *counts; is_valid_change(counts, (uint64_t *)coins, n, amount)
                       && total_coins(counts, 0, n) == \result) &&
    (\forall int *counts; is_valid_change(counts, (uint64_t *)coins, n, amount)
                       ==> total_coins(counts, 0, n) >= \result);
  // Case 2: impossible.
  ensures \result == -1 ==>
    (\forall int *counts; !is_valid_change(counts, (uint64_t *)coins, n, amount));
*/
int64_t coin_change(const uint64_t *coins, int n, uint64_t amount) {
  // Implement and verify coin_change here.
}
