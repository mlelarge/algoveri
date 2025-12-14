use vstd::prelude::*;

verus! {
    // Following is the block for necessary definitions
    // <preamble>
    spec fn is_valid_is(seq: Seq<i32>, indices: Seq<int>) -> bool {
        // Property 1: The indices themselves are strictly increasing.
        (forall|k: int, m: int|
            #![trigger indices[k], indices[m]]
            0 <= k < m < indices.len() ==> indices[k] < indices[m])
        &&
        // Property 2: All indices are valid (within the bounds of the original sequence).
        (forall|k: int|
            #![trigger indices[k]]
            0 <= k < indices.len() ==> 0 <= indices[k] < seq.len())
        &&
        // Property 3: The elements of the original sequence at these indices are strictly increasing.
        (forall|k: int, m: int|
            #![trigger seq[indices[k]], seq[indices[m]]]
            0 <= k < m < indices.len() ==> seq[indices[k]] < seq[indices[m]])
    }
    // </preamble>

    // Following is the block for potential helper specifications
    // <helpers>
    // This spec function formalizes the core invariant of our DP table.
    // It states that for a given index `k`, `dp[k]` is an upper bound on the length
    // of any increasing subsequence that ends at `seq[k]`.
    spec fn dp_is_upper_bound(s: Seq<i32>, dp: Seq<u64>, k: int) -> bool {
        forall|sub: Seq<int>|
            #![trigger is_valid_is(s, sub)]
            (is_valid_is(s, sub) && sub.len() > 0 && sub.last() == k) ==> (sub.len() <= dp[k])
    }
    // </helpers>

    // Following is the block for proofs of lemmas
    // <proofs>
    // Lemma 1: A prefix of a valid increasing subsequence is also a valid increasing subsequence.
    proof fn lemma_prefix_is_valid_is(seq: Seq<i32>, sub: Seq<int>)
        requires
            is_valid_is(seq, sub),
            sub.len() >= 1,
        ensures
            is_valid_is(seq, sub.drop_last()),
    {
        let prefix = sub.drop_last();
        assert forall|k: int, m: int| #![trigger prefix[k], prefix[m]] 0 <= k < m < prefix.len() implies prefix[k] < prefix[m] by {
            assert(sub[k] < sub[m]);
        }
        assert forall|k: int| #![trigger prefix[k]] 0 <= k < prefix.len() implies 0 <= prefix[k] < seq.len() by {
            assert(0 <= sub[k] < seq.len());
        }
        assert forall|k: int, m: int| #![trigger seq[prefix[k]], seq[prefix[m]]] 0 <= k < m < prefix.len() implies seq[prefix[k]] < seq[prefix[m]] by {
            assert(seq[sub[k]] < seq[sub[m]]);
        }
    }

    // Lemma 2: This is the core inductive step of the proof. It shows that if the DP table
    // is correct for all indices up to `i-1`, then our computation for `dp[i]` is also correct.
    proof fn lemma_dp_step_is_sound(seq: Seq<i32>, dp: Seq<u64>, i: int, new_dp_val: u64)
        requires
            0 <= i < seq.len(),
            dp.len() == seq.len(),
            (forall|k: int| 0 <= k < i ==> dp_is_upper_bound(seq, dp, k)),
            new_dp_val >= 1,
            (forall|j: int| (0 <= j < i && seq[j] < seq[i]) ==> new_dp_val >= dp[j] + 1),
        ensures
            (forall|sub: Seq<int>| #![trigger is_valid_is(seq, sub)] (is_valid_is(seq, sub) && sub.len() > 0 && sub.last() == i) ==> sub.len() <= new_dp_val),
    {
        assert forall|sub: Seq<int>|
            #![trigger is_valid_is(seq, sub)]
            is_valid_is(seq, sub) && sub.len() > 0 && sub.last() == i
        implies
            sub.len() <= new_dp_val
        by {
            if sub.len() == 1 {
                assert(sub.len() <= new_dp_val);
            } else {
                let prefix = sub.drop_last();
                lemma_prefix_is_valid_is(seq, sub);
                let j = prefix.last();

                assert(j < i);
                assert(seq[j] < seq[i]);
                assert(dp_is_upper_bound(seq, dp, j));
                assert(prefix.len() <= dp[j]);
                assert(sub.len() == prefix.len() + 1);
                assert(new_dp_val >= dp[j] + 1);
                assert(sub.len() <= new_dp_val);
            }
        };
    }
    // </proofs>

    // Following is the block for the main specification
    // <spec>
    fn longest_increasing_subsequence(seq: &Vec<i32>) -> (result: u64)
        requires
            seq.len() <= 0x7FFFFFFFFFFFFFFF,
        ensures
            forall|sub: Seq<int>| #[trigger] is_valid_is(seq@, sub) && sub.len() > 0 ==> sub.len() <= result,
    {
    // </spec>
    // <code>
        let n = seq.len();
        if n == 0 {
            proof {
                assert forall|sub: Seq<int>| #[trigger] is_valid_is(seq@, sub) && sub.len() > 0 implies sub.len() <= 0 by {
                    if is_valid_is(seq@, sub) && sub.len() > 0 {
                        assert(0 <= sub[0] < seq@.len());
                    }
                };
            }
            return 0;
        }

        let mut dp: Vec<u64> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                dp.len() == k,
                forall|i: int| 0 <= i < k ==> dp[i] == 1,
            decreases n - k,
        {
            dp.push(1);
            k += 1;
        }

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == seq.len(),
                seq@ == seq.view(),
                dp.len() == n,
                (forall|k: int| 0 <= k < i ==> dp_is_upper_bound(seq@, dp@, k)),
                (forall|k: int| 0 <= k < i ==> dp@[k] <= (k + 1) as u64),
            decreases n - i,
        {
            let mut current_max: u64 = 1;
            let mut j: usize = 0;
            let ghost dp_at_start_of_i = dp@;

            while j < i
                invariant
                    0 <= j <= i,
                    i < n,
                    seq.len() == n,
                    dp.len() == n,
                    dp@ == dp_at_start_of_i,
                    (forall|k: int| 0 <= k < i ==> dp@[k] <= (k + 1) as u64),
                    current_max >= 1,
                    current_max <= (i + 1) as u64,
                    (forall|k: int| (0 <= k < j && seq@[k] < seq@[i as int]) ==> current_max >= dp@[k] + 1),
                decreases i - j,
            {
                if seq[j] < seq[i] {
                    if current_max < dp[j] + 1 {
                        current_max = dp[j] + 1;
                    }
                }
                j += 1;
            }

            proof {
                assert forall |k: int| (0 <= k < i && seq@[k] < seq@[i as int]) implies current_max >= dp@[k] + 1 by {}
                lemma_dp_step_is_sound(seq@, dp_at_start_of_i, i as int, current_max);
            }

            dp.set(i, current_max);

            proof {
                assert forall |k: int| 0 <= k < i implies dp_is_upper_bound(seq@, dp@, k) by {
                    assert(dp_is_upper_bound(seq@, dp_at_start_of_i, k));
                }
                assert(dp_is_upper_bound(seq@, dp@, i as int));
                
                assert forall |k: int| 0 <= k < i + 1 implies dp@[k] <= (k + 1) as u64 by {
                    if k < i {
                        assert(dp@[k] == dp_at_start_of_i[k]);
                    } else { // k == i
                        assert(dp@[i as int] == current_max);
                        assert(current_max <= (i + 1) as u64);
                    }
                }
            }
            i += 1;
        }

        let mut max_len: u64 = 0;
        if n > 0 {
            max_len = dp[0];
        }

        let mut m: usize = 1;
        while m < n
            invariant
                1 <= m <= n,
                n == dp.len(),
                (forall|k: int| 0 <= k < m ==> max_len >= dp@[k]),
            decreases n - m,
        {
            if dp[m] > max_len {
                max_len = dp[m];
            }
            m += 1;
        }

        proof {
            assert forall|sub: Seq<int>| #[trigger] is_valid_is(seq@, sub) && sub.len() > 0 implies sub.len() <= max_len by {
                let k = sub.last();
                assert(0 <= k < seq.len());
                assert(dp_is_upper_bound(seq@, dp@, k));
                assert(sub.len() <= dp@[k]);
                assert(dp@[k] <= max_len);
            };
        }

        max_len
    }
    // </code>

    // 4. MAIN FUNCTION (External)
    #[verifier::external]
    fn main() {
        let mut v = Vec::new();
        v.push(10);
        v.push(2);
        v.push(5);
        v.push(3);
        v.push(7);
        v.push(101);
        v.push(18);

        let ans = longest_increasing_subsequence(&v);

        println!("The LIS length for {:?} is: {}", v, ans); // Expected: 4 ([2, 3, 7, 18] or [2, 5, 7, 18])
    }
}