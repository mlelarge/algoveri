#include <stdint.h>
#include <stddef.h>

/*@
  // Verus: pub open spec fn is_power_of_2(n: nat) -> bool decreases n
  //   n == 0 -> false; n == 1 -> true; else n % 2 == 0 && is_power_of_2(n / 2).
  axiomatic IsPowerOf2 {
    predicate is_power_of_2{L}(integer n) reads \nothing;

    axiom is_power_of_2_zero{L}:
      !is_power_of_2(0);

    axiom is_power_of_2_one{L}:
      is_power_of_2(1);

    axiom is_power_of_2_step{L}:
      \forall integer n; n >= 2 ==>
        (is_power_of_2(n) <==> (n % 2 == 0 && is_power_of_2(n / 2)));
  }

  // Verus: pub open spec fn coeffs_bounded(s: Seq<int>) -> bool
  predicate coeffs_bounded{L}(int64_t *a, integer n) =
    \valid_read(a + (0 .. n - 1)) &&
    (\forall integer i; 0 <= i < n ==> -1000000 <= a[i] <= 1000000);

  // Verus: pub open spec fn spec_convolution_sum(a, b, k, current_i) -> int
  //   decreases current_i + 1
  // Verus: pub open spec fn spec_poly_mul_coeff(a, b, k) -> int =
  //   spec_convolution_sum(a, b, k, k).
  axiomatic PolyMulKaratsuba {
    logic integer spec_convolution_sum{L}(int64_t *a, integer na,
                                          int64_t *b, integer nb,
                                          integer k, integer i)
      reads a[0 .. na - 1], b[0 .. nb - 1];

    axiom spec_convolution_sum_base{L}:
      \forall int64_t *a, integer na, int64_t *b, integer nb, integer k, integer i;
        i < 0 ==> spec_convolution_sum(a, na, b, nb, k, i) == 0;

    axiom spec_convolution_sum_step{L}:
      \forall int64_t *a, integer na, int64_t *b, integer nb, integer k, integer i;
        i >= 0 ==>
          spec_convolution_sum(a, na, b, nb, k, i) ==
            ((0 <= i < na && 0 <= k - i < nb) ? a[i] * b[k - i] : 0) +
            spec_convolution_sum(a, na, b, nb, k, i - 1);

    logic integer spec_poly_mul_coeff{L}(int64_t *a, integer na,
                                         int64_t *b, integer nb,
                                         integer k)
      reads a[0 .. na - 1], b[0 .. nb - 1];

    axiom spec_poly_mul_coeff_def{L}:
      \forall int64_t *a, integer na, int64_t *b, integer nb, integer k;
        spec_poly_mul_coeff(a, na, b, nb, k) ==
          spec_convolution_sum(a, na, b, nb, k, k);
  }
*/

/*@
  // Verus: fn poly_multiply(a: Vec<i64>, b: Vec<i64>) -> (res: Vec<i64>)
  //   requires a.len() > 0, b.len() > 0, a.len() + b.len() <= 1000,
  //            is_power_of_2(a.len()), is_power_of_2(b.len()),
  //            a.len() == b.len(),
  //            coeffs_bounded(to_int(a@)), coeffs_bounded(to_int(b@))
  //   ensures res.len() == a.len() + b.len() - 1,
  //           forall k. res[k] == spec_poly_mul_coeff(to_int(a@), to_int(b@), k).
  requires 0 < n;
  requires 2 * n <= 1000;
  requires is_power_of_2(n);
  requires coeffs_bounded((int64_t *)a, n);
  requires coeffs_bounded((int64_t *)b, n);
  requires \valid(out + (0 .. 2 * n - 2));
  assigns out[0 .. 2 * n - 2];
  ensures \forall integer k; 0 <= k < 2 * n - 1 ==>
            out[k] == spec_poly_mul_coeff((int64_t *)a, n, (int64_t *)b, n, k);
*/
void poly_multiply(const int64_t *a, int n,
                   const int64_t *b,
                   int64_t *out) {
  // Implement and verify poly_multiply here.
}
