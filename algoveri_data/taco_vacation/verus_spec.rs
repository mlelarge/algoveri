use vstd::prelude::*;

verus! {

pub struct Input {
    pub n: usize,
    pub a: Vec<u64>,
    pub b: Vec<u64>,
    pub c: Vec<u64>,
}

spec fn max(a: int, b: int) -> int {
    if a > b { a } else { b }
}

spec fn max3(a: int, b: int, c: int) -> int {
    max(a, max(b, c))
}

spec fn get_gain(day_idx: int, activity: int, a: Seq<u64>, b: Seq<u64>, c: Seq<u64>) -> int {
    if day_idx >= 0 && day_idx < a.len() && day_idx < b.len() && day_idx < c.len() {
        if activity == 0 {
            a[day_idx] as int
        } else if activity == 1 {
            b[day_idx] as int
        } else {
            c[day_idx] as int
        }
    } else {
        0 
    }
}

spec fn max_happiness_spec(day_idx: int, activity: int, a: Seq<u64>, b: Seq<u64>, c: Seq<u64>) -> int 
    decreases day_idx
{
    if day_idx < 0 {
        0
    } else {
        let gain = get_gain(day_idx, activity, a, b, c);
        
        let prev_max = if day_idx == 0 {
            0
        } else {
            if activity == 0 {
                max(max_happiness_spec(day_idx - 1, 1, a, b, c), max_happiness_spec(day_idx - 1, 2, a, b, c))
            } else if activity == 1 {
                max(max_happiness_spec(day_idx - 1, 0, a, b, c), max_happiness_spec(day_idx - 1, 2, a, b, c))
            } else {
                max(max_happiness_spec(day_idx - 1, 0, a, b, c), max_happiness_spec(day_idx - 1, 1, a, b, c))
            }
        };
        
        prev_max + gain
    }
}

fn solve_taco_vacation(input: &Input) -> (result: u64)
    requires
        input.n >= 1,
        input.n <= 100000,
        input.a.len() == input.n,
        input.b.len() == input.n,
        input.c.len() == input.n,
    ensures
        // result is the max of ending with any of the 3 activities on the last day (matrix N-1)
        result == max3(
            max_happiness_spec(input.n as int - 1, 0, input.a@, input.b@, input.c@),
            max_happiness_spec(input.n as int - 1, 1, input.a@, input.b@, input.c@),
            max_happiness_spec(input.n as int - 1, 2, input.a@, input.b@, input.c@)
        ),
{
    // TODO: Implement DP
    // Placeholder
    0
}

} // verus!
