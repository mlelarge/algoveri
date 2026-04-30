#include <stdint.h>
#include <stddef.h>

/*@
  // Verus: pub open spec fn coeffs_bounded(s: Seq<int>) -> bool
  //   forall i in [0, len), -1_000_000 <= s[i] <= 1_000_000.
  predicate coeffs_bounded{L}(int64_t *a, integer n) =
    \valid_read(a + (0 .. n - 1)) &&
    (\forall integer i; 0 <= i < n ==> -1000000 <= a[i] <= 1000000);

  // Verus: pub open spec fn spec_convolution_sum(a, b, k, current_i) -> int
  //   decreases current_i + 1
  //   if current_i < 0 { 0 } else { term(a, b, k, current_i) + sum(a, b, k, current_i - 1) }
  //   where term = a[i] * b[k - i] when both indices in range, else 0.
  // Verus: pub open spec fn spec_poly_mul_coeff(a, b, k) -> int =
  //   spec_convolution_sum(a, b, k, k).
  axiomatic PolyMulNaive {
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
  //            coeffs_bounded(to_int(a@)), coeffs_bounded(to_int(b@))
  //   ensures res.len() == a.len() + b.len() - 1,
  //           forall k. res[k] == spec_poly_mul_coeff(to_int(a@), to_int(b@), k).
  requires 0 < na;
  requires 0 < nb;
  requires na + nb <= 1000;
  requires coeffs_bounded((int64_t *)a, na);
  requires coeffs_bounded((int64_t *)b, nb);
  requires \valid(out + (0 .. na + nb - 2));
  // Verus's &mut/& on disjoint Vecs gives non-aliasing for free; ACSL must state it.
  requires \separated(out + (0 .. na + nb - 2), a + (0 .. na - 1));
  requires \separated(out + (0 .. na + nb - 2), b + (0 .. nb - 1));
  assigns out[0 .. na + nb - 2];
  ensures \forall integer k; 0 <= k < na + nb - 1 ==>
            out[k] == spec_poly_mul_coeff((int64_t *)a, na, (int64_t *)b, nb, k);
*/
void poly_multiply(const int64_t *a, int na,
                   const int64_t *b, int nb,
                   int64_t *out) {
  // Implement and verify poly_multiply here.
}
