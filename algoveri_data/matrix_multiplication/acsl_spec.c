#include <stdint.h>
#include <stddef.h>

/*@
  // Verus: spec fn is_valid_matrix(m, rows, cols)
  //   m.len() == rows && forall i. 0 <= i < rows ==> m[i].len() == cols.
  // C: matrices flattened row-major. valid_matrix_a/b also encodes the
  // Verus value bound A[i][j] <= 100 / B[i][j] <= 100.
  predicate valid_matrix_a{L}(uint64_t *a, integer rows, integer mid) =
    0 < rows <= 10 &&
    0 < mid <= 10 &&
    \valid_read(a + (0 .. rows * mid - 1)) &&
    (\forall integer i; 0 <= i < rows * mid ==> a[i] <= 100);

  predicate valid_matrix_b{L}(uint64_t *b, integer mid, integer cols) =
    0 < mid <= 10 &&
    0 < cols <= 10 &&
    \valid_read(b + (0 .. mid * cols - 1)) &&
    (\forall integer i; 0 <= i < mid * cols ==> b[i] <= 100);

  // Verus: spec fn dot_product(row_vals, B_vals, c, k) -> int decreases k
  //   k <= 0 -> 0;
  //   else row_vals[k-1] * B_vals[k-1][c] + dot_product(row_vals, B_vals, c, k-1).
  axiomatic MatMulDot {
    logic integer dot_product{L}(uint64_t *a, uint64_t *b,
                                 integer mid, integer cols,
                                 integer r, integer c, integer k)
      reads a[0 .. r * mid + mid - 1], b[0 .. (mid - 1) * cols + c];

    axiom dot_product_base{L}:
      \forall uint64_t *a, uint64_t *b, integer mid, integer cols,
              integer r, integer c, integer k;
        k <= 0 ==> dot_product(a, b, mid, cols, r, c, k) == 0;

    axiom dot_product_step{L}:
      \forall uint64_t *a, uint64_t *b, integer mid, integer cols,
              integer r, integer c, integer k;
        k > 0 ==>
          dot_product(a, b, mid, cols, r, c, k) ==
            a[r * mid + (k - 1)] * b[(k - 1) * cols + c] +
            dot_product(a, b, mid, cols, r, c, k - 1);
  }
*/


/*@
  // Verus: fn matrix_multiply(A: &Vec<Vec<u64>>, B: &Vec<Vec<u64>>) -> (C: Vec<Vec<u64>>)
  //   requires A.len() > 0, B.len() > 0, A[0].len() == B.len(),
  //            A.len() <= 10, B.len() <= 10, B[0].len() <= 10,
  //            uniform row lengths, A[i][j] <= 100, B[i][j] <= 100
  //   ensures  C.len() == A.len(), C[0].len() == B[0].len(),
  //            forall i, j. C[i][j] == dot_product(A[i], B, j, B.len()).
  // C: A is rows x mid, B is mid x cols, C is rows x cols, flat row-major.
  requires valid_matrix_a((uint64_t *)a, rows, mid);
  requires valid_matrix_b((uint64_t *)b, mid, cols);
  requires \valid(c + (0 .. rows * cols - 1));
  assigns c[0 .. rows * cols - 1];
  ensures \forall integer r, col;
            0 <= r < rows && 0 <= col < cols ==>
            c[r * cols + col] ==
              dot_product((uint64_t *)a, (uint64_t *)b, mid, cols, r, col, mid);
*/
void matrix_multiply(const uint64_t *a, int rows, int mid,
                     const uint64_t *b, int cols,
                     uint64_t *c) {
  // Implement and verify matrix_multiply here.
}
