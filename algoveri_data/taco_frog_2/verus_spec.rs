use vstd::prelude::*;

verus! {

// Removed external_body
pub struct Input {
    pub n: usize,
    pub k: usize,
    pub heights: Vec<int>,
}

spec fn abs_diff(a: int, b: int) -> int {
    if a > b { a - b } else { b - a }
}

spec fn min(a: int, b: int) -> int {
    if a < b { a } else { b }
}

spec fn min_cost_spec(target_idx: int, k: int, heights: Seq<int>) -> int 
    decreases target_idx, k + 2
{
    if target_idx <= 0 {
        0
    } else if k < 1 { // Ensure k is positive for measure logic
        0
    } else {
        min_over_j(target_idx, k, 1, heights)
    }
}

spec fn min_over_j(target_idx: int, k: int, current_j: int, heights: Seq<int>) -> int
    decreases target_idx, k - current_j
{
    if k < 1 {
        1000000000
    } else if current_j > k || target_idx - current_j < 0 {
        1000000000 
    } else {
        if current_j < 1 {
            1000000000
        } else {
            // Bounds check
            if target_idx < heights.len() && target_idx >= 0 && target_idx - current_j < heights.len() {
                 let prev_idx = target_idx - current_j;
                 
                 // termination relies on prev_idx < target_idx, which is true since current_j >= 1
                 if prev_idx >= 0 && prev_idx < heights.len() {
                     let cost = min_cost_spec(prev_idx, k, heights) + abs_diff(heights[target_idx], heights[prev_idx]);
                     
                     if current_j == k || target_idx - (current_j + 1) < 0 {
                         cost
                     } else {
                         min(cost, min_over_j(target_idx, k, current_j + 1, heights))
                     }
                 } else {
                     1000000000
                 }
            } else {
                 1000000000
            }
        }
    }
}

fn solve_taco_frog_2(input: &Input) -> (min_cost: i64)
    requires
        input.n >= 2,
        input.k >= 1,
        input.heights.len() == input.n,
    ensures
        min_cost == min_cost_spec(input.n as int - 1, input.k as int, input.heights@),
{
    // TODO: Implement DP
    // Placeholder
    0i64
}

} // verus!
