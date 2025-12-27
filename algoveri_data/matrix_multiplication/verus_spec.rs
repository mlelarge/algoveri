use vstd::prelude::*;

verus! {
    // Following is the block for necessary definitions
    // <preamble>
    
    // Calculate dot product of row A[r] and col B[c]
    // A_row: sequence of values in A's row r
    // B: the whole matrix B
    // c: the column index in B
    // k: the length of the dot product (number of columns in A / rows in B)
    spec fn dot_product(row_vals: Seq<int>, B_vals: Seq<Seq<int>>, c: int, k: int) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            // k-1 is the current index we are summing
            row_vals[k-1] * B_vals[k-1][c] + dot_product(row_vals, B_vals, c, k-1)
        }
    }

    // Helper to check if a matrix is valid (all rows have same length 'cols')
    spec fn is_valid_matrix(m: Seq<Seq<int>>, rows: int, cols: int) -> bool {
        m.len() == rows &&
        (forall|i: int| 0 <= i < rows ==> m[i].len() == cols)
    }
    // </preamble>

    // Following is the block for potential helper specifications
    // <helpers>
    spec fn vec_vec_u64_to_int(m: Seq<Seq<u64>>) -> Seq<Seq<int>> {
        m.map(|i, row: Seq<u64>| row.map(|j, val| val as int))
    }
    // </helpers>

    // Following is the block for proofs of lemmas
    // <proofs>

    // </proofs>

    // Following is the block for the main specification
    // <spec>
    fn matrix_multiply(A: &Vec<Vec<u64>>, B: &Vec<Vec<u64>>) -> (C: Vec<Vec<u64>>)
        requires
            A.len() > 0,
            B.len() > 0,
            A[0].len() == B.len(), // cols A == rows B
            A.len() <= 10, // Small bounds to keep verification manageable
            B.len() <= 10,
            B[0].len() <= 10,
            // A is a valid n x m matrix
            forall|i: int| 0 <= i < A.len() ==> A[i].len() == B.len(),
            // B is a valid m x k matrix
            forall|i: int| 0 <= i < B.len() ==> B[i].len() == B[0].len(),
            // Value bounds
            forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[i].len() ==> A[i][j] <= 100,
            forall|i: int, j: int| 0 <= i < B.len() && 0 <= j < B[i].len() ==> B[i][j] <= 100,

        ensures
            C.len() == A.len(),
            C.len() > 0 ==> C[0].len() == B[0].len(),
            // Result C is valid Size(A) x Size(B[0])
            is_valid_matrix(vec_vec_u64_to_int(C@), A.len() as int, B[0].len() as int),
            // Each element is the dot product
            forall|i: int, j: int| #![trigger C[i][j]] 0 <= i < C.len() && 0 <= j < C[0].len() 
                ==> C[i][j] == dot_product(
                        vec_vec_u64_to_int(A@)[i], 
                        vec_vec_u64_to_int(B@), 
                        j, 
                        B.len() as int),
    // </spec>
    // <code>
    {
        // TODO: Implement Matrix Multiplication
    }
    // </code>

    #[verifier::external]
    fn main() {
        let mut A = Vec::new();
        let mut row1 = Vec::new(); row1.push(1); row1.push(2);
        let mut row2 = Vec::new(); row2.push(3); row2.push(4);
        A.push(row1); A.push(row2); // 2x2
        
        let mut B = Vec::new();
        let mut brow1 = Vec::new(); brow1.push(2); brow1.push(0);
        let mut brow2 = Vec::new(); brow2.push(1); brow2.push(2);
        B.push(brow1); B.push(brow2); // 2x2
        
        // C = [[4, 4], [10, 8]]
        let C = matrix_multiply(&A, &B);
        println!("C[0][0] = {}", C[0][0]);
    }
}
