#include <limits.h>
#include <stddef.h>

/*@
  // Verus: pub open spec fn char_weight(c: u8) -> int
  //   '(' (40) -> 1, ')' (41) -> -1, otherwise 0.
  logic integer char_weight(unsigned char c) =
    c == 40 ? 1 :
    c == 41 ? -1 :
    0;

  // Verus: pub open spec fn total_weight(s: Seq<u8>) -> int  decreases s.len()
  //   sum of char_weight over s[0..len].
  axiomatic TotalWeight {
    logic integer total_weight{L}(unsigned char *s, integer n)
      reads s[0 .. n - 1];

    axiom total_weight_base{L}:
      \forall unsigned char *s; total_weight(s, 0) == 0;

    axiom total_weight_step{L}:
      \forall unsigned char *s, integer n;
        n > 0 ==>
          total_weight(s, n) == total_weight(s, n - 1) + char_weight(s[n - 1]);
  }

  // Verus: pub open spec fn valid_prefix_weights(s) -> bool
  //   forall i in [0, len], total_weight(s.subrange(0, i)) >= 0.
  predicate valid_prefix_weights{L}(unsigned char *s, integer n) =
    \forall integer i; 0 <= i <= n ==> total_weight(s, i) >= 0;

  // Verus: pub open spec fn is_matched(s) -> bool
  //   total_weight(s) == 0 && valid_prefix_weights(s).
  predicate is_matched{L}(unsigned char *s, integer n) =
    total_weight(s, n) == 0 && valid_prefix_weights(s, n);
*/

/*@
  // Verus: fn bracket_match(s: Seq<u8>) -> (res: bool)
  //   requires s.len() <= 1_000_000
  //   ensures res == is_matched(s)
  requires 0 <= n <= 1000000;
  requires n == 0 || \valid_read(s + (0 .. n - 1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures \result == 1 <==> is_matched((unsigned char *)s, n);
*/
int bracket_match(const unsigned char *s, int n) {
  // Implement and verify bracket_match here.
}
