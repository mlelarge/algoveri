#include <stdint.h>
#include <stddef.h>

/*@
  // Verus: spec fn is_valid_is(seq: Seq<i32>, indices: Seq<int>) -> bool
  //   indices strictly increasing,
  //   each index in [0, seq.len()),
  //   and seq values strictly increase along the index sequence.
  // C: indices passed as (idx, k) parallel slice of length k.
  predicate is_valid_is{L}(int32_t *seq, integer n,
                           int *indices, integer k) =
    (\forall integer i, j; 0 <= i < j < k ==> indices[i] < indices[j]) &&
    (\forall integer i; 0 <= i < k ==> 0 <= indices[i] < n) &&
    (\forall integer i, j; 0 <= i < j < k ==> seq[indices[i]] < seq[indices[j]]);
*/


/*@
  // Verus: fn longest_increasing_subsequence(seq: &Vec<i32>) -> (result: u64)
  //   requires seq.len() <= 0x7FFFFFFFFFFFFFFF
  //   ensures forall sub. is_valid_is(seq@, sub) && sub.len() > 0 ==> sub.len() <= result,
  //           exists sub. is_valid_is(seq@, sub) && sub.len() == result.
  requires 0 <= n <= 3000;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  assigns \nothing;
  ensures 0 <= \result <= n;
  ensures \forall int *idx, integer k;
            is_valid_is((int32_t *)a, n, idx, k) && k > 0 ==> k <= \result;
  ensures \exists int *idx, integer k;
            is_valid_is((int32_t *)a, n, idx, k) && k == \result;
*/
int longest_increasing_subsequence(const int32_t *a, int n) {
  // Implement and verify longest_increasing_subsequence here.
}
