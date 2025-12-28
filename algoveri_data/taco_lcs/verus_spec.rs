use vstd::prelude::*;

verus! {

// #[verifier(external_body)] // Removed
pub struct Input {
    pub s: Vec<char>,
    pub t: Vec<char>,
}

spec fn max(a: int, b: int) -> int {
    if a > b {
        a
    } else {
        b
    }
}

spec fn lcs_len_spec(i: int, j: int, s: Seq<char>, t: Seq<char>) -> int
    decreases i, j
{
    if i <= 0 || j <= 0 {
        0
    } else {
        // Safe access check included in logic for robustness, though recursion naturally bounds it.
        // If s[i-1] == t[j-1], we add 1.
        if i - 1 < s.len() && j - 1 < t.len() && s[i - 1] == t[j - 1] {
            1 + lcs_len_spec(i - 1, j - 1, s, t)
        } else {
            max(
                lcs_len_spec(i - 1, j, s, t),
                lcs_len_spec(i, j - 1, s, t)
            )
        }
    }
}

fn solve_taco_lcs(input: &Input) -> (len: usize)
    requires
        input.s.len() <= 3000,
        input.t.len() <= 3000,
    ensures
        len as int == lcs_len_spec(input.s.len() as int, input.t.len() as int, input.s@, input.t@),
{
    // TODO: Implement DP
    // Placeholder for verified implementation.
    0
}

} // verus!
