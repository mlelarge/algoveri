#include <stdint.h>
#include <stddef.h>

/*@
  // Verus: pub open spec fn add_gf2(a, b) -> int = (a + b) % 2
  logic integer add_gf2(integer a, integer b) = (a + b) % 2;
  // Verus: pub open spec fn mul_gf2(a, b) -> int = (a * b) % 2
  logic integer mul_gf2(integer a, integer b) = (a * b) % 2;

  // Verus: pub open spec fn is_binary_vector(v: Seq<int>) -> bool
  predicate is_binary_vector{L}(uint64_t *v, integer n) =
    \valid_read(v + (0 .. n - 1)) &&
    (\forall integer i; 0 <= i < n ==> v[i] == 0 || v[i] == 1);

  // Verus: pub open spec fn is_binary_matrix(m, rows, cols) -> bool
  // C: matrix flattened row-major.
  predicate is_binary_matrix{L}(uint64_t *a, integer rows, integer cols) =
    0 < rows <= 100 &&
    0 < cols <= 100 &&
    \valid_read(a + (0 .. rows * cols - 1)) &&
    (\forall integer i, j; 0 <= i < rows && 0 <= j < cols ==>
       a[i * cols + j] == 0 || a[i * cols + j] == 1);

  // Verus: pub open spec fn spec_dot_product_gf2(row, x, k) -> int decreases k+1
  //   k < 0 -> 0; else (when k in range)
  //     add_gf2(mul_gf2(row[k], x[k]), dot(row, x, k-1));
  //   else dot(row, x, k-1).
  // C: row is the `row`-th row of matrix a (flattened, cols-wide); x has length `cols`.
  axiomatic DotProductGF2 {
    logic integer dot_product_gf2{L}(uint64_t *a, uint64_t *x,
                                     integer cols, integer row, integer k)
      reads a[row * cols .. row * cols + cols - 1], x[0 .. cols - 1];

    axiom dot_product_gf2_base{L}:
      \forall uint64_t *a, uint64_t *x, integer cols, integer row, integer k;
        k < 0 ==> dot_product_gf2(a, x, cols, row, k) == 0;

    axiom dot_product_gf2_step{L}:
      \forall uint64_t *a, uint64_t *x, integer cols, integer row, integer k;
        0 <= k < cols ==>
          dot_product_gf2(a, x, cols, row, k) ==
            add_gf2(mul_gf2(a[row * cols + k], x[k]),
                    dot_product_gf2(a, x, cols, row, k - 1));

    axiom dot_product_gf2_skip{L}:
      \forall uint64_t *a, uint64_t *x, integer cols, integer row, integer k;
        k >= cols ==>
          dot_product_gf2(a, x, cols, row, k) ==
            dot_product_gf2(a, x, cols, row, k - 1);
  }

  // Verus: pub open spec fn is_solution(a, b, x) -> bool
  //   a.len() == b.len() && a.len() > 0 && x.len() == a[0].len()
  //   && is_binary_vector(x)
  //   && forall i. spec_dot_product_gf2(a[i], x, x.len() - 1) == b[i].
  predicate is_solution{L}(uint64_t *a, uint64_t *b,
                           integer rows, integer cols, uint64_t *x) =
    rows > 0 && cols > 0 &&
    is_binary_vector(x, cols) &&
    (\forall integer i; 0 <= i < rows ==>
       dot_product_gf2(a, x, cols, i, cols - 1) == b[i]);
*/


/*@
  // Verus: fn solve_linear_system_gf2(matrix: Vec<Vec<u64>>, b: Vec<u64>)
  //          -> (res: Option<Vec<u64>>)
  //   requires matrix.len() > 0, matrix[0].len() > 0, matrix.len() == b.len(),
  //            matrix.len() <= 100, matrix[0].len() <= 100,
  //            is_binary_matrix(matrix), is_binary_vector(b)
  //   ensures  Some(x) -> is_solution(matrix, b, x);
  //            None    -> forall x. binary && length-cols ==> !is_solution(matrix, b, x).
  // C: \result is 0 (None) or 1 (Some); on Some, x_out holds the solution.
  requires is_binary_matrix((uint64_t *)a, rows, cols);
  requires is_binary_vector((uint64_t *)b, rows);
  requires \valid(x_out + (0 .. cols - 1));
  assigns x_out[0 .. cols - 1];
  ensures \result == 0 || \result == 1;
  ensures \result == 1 ==> is_solution((uint64_t *)a, (uint64_t *)b, rows, cols, x_out);
  ensures \result == 0 ==>
            \forall uint64_t *x;
              is_binary_vector(x, cols) ==>
                !is_solution((uint64_t *)a, (uint64_t *)b, rows, cols, x);
*/
int solve_linear_system_gf2(const uint64_t *a, const uint64_t *b,
                            int rows, int cols, uint64_t *x_out) {
  // Implement and verify solve_linear_system_gf2 here.
}
