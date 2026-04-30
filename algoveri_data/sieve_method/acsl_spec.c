#include <stdbool.h>
#include <stddef.h>

/*@
  predicate divides(integer d, integer n) =
    d != 0 && n % d == 0;

  predicate is_prime(integer n) =
    n > 1 && \forall integer d; 1 < d < n ==> !divides(d, n);
*/

/*@
  // Verus: fn sieve_of_eratosthenes(n: usize) -> (primes: Vec<bool>) with primes.len() == n
  // C: caller-provided output buffer of length n.
  requires 0 <= n <= 100000;
  requires n == 0 || \valid(primes + (0 .. n - 1));
  assigns primes[0 .. n - 1];
  ensures \forall integer i; 0 <= i < n ==>
    ((primes[i] != 0) <==> is_prime(i));
*/
void sieve_of_eratosthenes(size_t n, bool *primes) {
  // Implement and verify sieve_of_eratosthenes here.
}
