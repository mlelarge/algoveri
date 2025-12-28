use vstd::prelude::*;

verus! {

// #[verifier(external_body)] // Removed
pub struct Input {
    pub n: usize,
    pub heights: Vec<int>,
}

spec fn abs_diff(a: int, b: int) -> int {
    if a > b {
        a - b
    } else {
        b - a
    }
}

spec fn min(a: int, b: int) -> int {
    if a < b {
        a
    } else {
        b
    }
}

// Spec function to define the optimal cost to reach stone `target_idx` (0-indexed)
spec fn min_cost_spec(target_idx: int, heights: Seq<int>) -> int 
    decreases target_idx
{
    if target_idx <= 0 {
        0
    } else if target_idx == 1 {
        abs_diff(heights[1], heights[0])
    } else {
        min(
            min_cost_spec(target_idx - 1, heights) + abs_diff(heights[target_idx], heights[target_idx - 1]),
            min_cost_spec(target_idx - 2, heights) + abs_diff(heights[target_idx], heights[target_idx - 2])
        )
    }
}

fn solve_taco_frog_1(input: &Input) -> (min_cost: i64)
    requires
        input.n >= 2,
        input.heights.len() == input.n,
    ensures
        min_cost == min_cost_spec(input.n as int - 1, input.heights@),
{
    // TODO: Implement DP
    // Placeholder
    0i64
}

} // verus!
