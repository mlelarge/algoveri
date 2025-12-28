use vstd::prelude::*;

verus! {

// Removed external_body
pub struct Input {
    pub h: usize,
    pub w: usize,
    pub grid: Vec<Vec<char>>,
}

spec fn is_valid(i: int, j: int, grid: Seq<Seq<char>>) -> bool {
    0 <= i < grid.len() && 0 <= j < grid[i].len() && grid[i][j] == '.'
}

spec fn count_paths_spec(i: int, j: int, grid: Seq<Seq<char>>) -> int
    decreases i, j
{
    if i < 0 || j < 0 {
        0
    } else if i == 0 && j == 0 {
        1
    } else if !is_valid(i, j, grid) {
        0
    } else {
        // Only recurse if index strictly positive to ensure measure (i,j) decreases wrt well-founded order on Nats
        // Actually (i, j) decreases in lexicographic order on Integers is NOT well founded.
        // We rely on the fact that if i=0, we don't assume i-1 is "smaller" in a bounded way.
        // By guarding, we ensure we don't follow the infinite descent chain.
        let from_top = if i > 0 { count_paths_spec(i - 1, j, grid) } else { 0 };
        let from_left = if j > 0 { count_paths_spec(i, j - 1, grid) } else { 0 };
        from_top + from_left
    }
}

fn solve_taco_grid_1(input: &Input) -> (count: u64)
    requires
        input.h >= 2,
        input.w >= 2,
        input.grid.len() == input.h,
        forall|i: int| #![trigger input.grid[i]] 0 <= i < input.h ==> input.grid[i].len() == input.w,
        input.grid[0].len() > 0,
        input.grid[0][0] == '.',
        
    ensures
        count as int == count_paths_spec(input.h as int - 1, input.w as int - 1, input.grid@.map_values(|r: Vec<char>| r@)) % 1000000007,
{
    // TODO: Implement DP
    // Placeholder
    0u64
}

} // verus!
