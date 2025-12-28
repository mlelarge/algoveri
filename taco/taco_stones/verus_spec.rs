use vstd::prelude::*;

verus! {

pub struct Input {
    pub n: usize,
    pub k: usize,
    pub a: Vec<usize>,
}

spec fn can_win_spec(stones: int, moves: Seq<usize>) -> bool 
    decreases stones, (moves.len() + 1) as int
{
    if stones <= 0 {
        false
    } else {
        exists_losing_move_for_opponent(stones, moves, 0)
    }
}

spec fn exists_losing_move_for_opponent(stones: int, moves: Seq<usize>, idx: int) -> bool 
    decreases stones, (moves.len() - idx) as int
{
    if idx < 0 || idx >= moves.len() {
        false
    } else {
        let m = moves[idx] as int;
        // Logic requires m > 0 for termination
        if m > 0 && stones >= m && !can_win_spec(stones - m, moves) {
            true
        } else {
            exists_losing_move_for_opponent(stones, moves, idx + 1)
        }
    }
}

fn solve_taco_stones(input: &Input) -> (taro_wins: bool)
    requires
        input.n >= 1,
        input.k >= 1,
        input.a.len() == input.n,
    ensures
        taro_wins == can_win_spec(input.k as int, input.a@),
{
    // TODO: Implement DP
    // Placeholder
    false
}

} // verus!
