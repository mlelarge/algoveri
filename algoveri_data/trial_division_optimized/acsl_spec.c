#include <stdint.h>

/*@
  // Verus: pub open spec fn divides(d: int, n: int) -> bool { n % d == 0 }
  predicate divides(integer d, integer n) =
    d != 0 && n % d == 0;

  // Verus: pub open spec fn is_prime(n: int) -> bool
  //   n > 1 && forall|d: int| 1 < d < n ==> !divides(d, n)
  predicate is_prime(integer n) =
    n > 1 && (\forall integer d; 1 < d < n ==> !divides(d, n));
*/


/*@
  // Verus: fn check_prime(n: u64) -> (res: bool) ensures res == is_prime(n as int)
  // Optimized variant: implementation tests divisors only up to sqrt(n).
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures \result == 1 <==> is_prime(n);
*/
int check_prime(uint64_t n) {
  // Implement and verify check_prime here.
}
