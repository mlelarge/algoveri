#include <limits.h>
#include <stdint.h>

/*@
  axiomatic GcdModel {
    logic integer spec_gcd(integer a, integer b);

    axiom spec_gcd_base:
      \forall integer a; a >= 0 ==> spec_gcd(a, 0) == a;

    axiom spec_gcd_step:
      \forall integer a, b;
        a >= 0 && b > 0 ==> spec_gcd(a, b) == spec_gcd(b, a % b);
  }
*/

/*@
  assigns \nothing;
  ensures \result == spec_gcd(a, b);
*/
uint64_t compute_gcd(uint64_t a, uint64_t b) {
  // Implement and verify compute_gcd here.
}
