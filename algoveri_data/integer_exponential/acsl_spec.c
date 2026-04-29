#include <limits.h>
#include <stdint.h>

/*@
  // Verus: pub open spec fn spec_pow(b: nat, e: nat) -> nat
  //   decreases e
  //   if e == 0 { 1 } else { b * spec_pow(b, (e - 1) as nat) }
  axiomatic IntegerExp {
    logic integer spec_pow(integer b, integer e);

    axiom spec_pow_base:
      \forall integer b; spec_pow(b, 0) == 1;

    axiom spec_pow_step:
      \forall integer b, e;
        e > 0 ==> spec_pow(b, e) == b * spec_pow(b, e - 1);
  }
*/


/*@
  // Verus: fn exponentiation(b: u64, e: u64) -> (res: u64)
  //   requires spec_pow(b as nat, e as nat) <= 0xffff_ffff_ffff_ffff
  //   ensures  res == spec_pow(b as nat, e as nat)
  requires b >= 0 && e >= 0;
  requires spec_pow(b, e) <= ULLONG_MAX;
  assigns \nothing;
  ensures \result == spec_pow(b, e);
*/
uint64_t exponentiation(uint64_t b, uint64_t e) {
  // Implement and verify exponentiation here.
}
