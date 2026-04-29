#include <limits.h>
#include <stddef.h>

/*@
  // Verus: spec fn matches_at(haystack: Seq<u8>, needle: Seq<u8>, start_index: int) -> bool
  predicate matches_at{L}(unsigned char *haystack,
                          integer hay_len,
                          unsigned char *needle,
                          integer needle_len,
                          integer start_index) =
    0 <= start_index &&
    0 <= needle_len &&
    start_index + needle_len <= hay_len &&
    (\forall integer i; 0 <= i < needle_len ==>
       haystack[start_index + i] == needle[i]);

  // Verus: spec fn patterns_view(patterns: Vec<Vec<u8>>) -> Seq<Seq<u8>>
  //   In C, the pattern set is passed as parallel arrays patterns[pid] / pat_lens[pid].
  //   well_formed_patterns asserts each pattern slice is readable.
  predicate well_formed_patterns{L}(unsigned char **patterns,
                                    int *pat_lens,
                                    integer pat_count) =
    \forall integer pid;
      0 <= pid < pat_count ==>
        0 <= pat_lens[pid] < 1000000 &&
        (pat_lens[pid] == 0 ||
         \valid_read(patterns[pid] + (0 .. pat_lens[pid] - 1)));
*/

/*@
  // Verus: fn ac_automata_search(haystack: &Vec<u8>, patterns: &Vec<Vec<u8>>)
  //          -> (results: Vec<(usize, usize)>)
  //   requires patterns.len() > 0,
  //            haystack.len() < 1_000_000,
  //            patterns.len() < 1_000_000,
  //            forall i, patterns[i].len() < 1_000_000
  //   ensures soundness: every (pid, idx) in results satisfies
  //              0 <= pid < patterns.len() && matches_at(haystack, patterns[pid], idx),
  //           completeness: every (pid, idx) such that
  //              0 <= pid < patterns.len() && matches_at(haystack, patterns[pid], idx)
  //              is contained in results.
  // C: results are returned in two parallel arrays out_pids[k], out_idxs[k] of length
  //    \result; the caller pre-allocates max_results entries.
  requires 0 <= hay_len < 1000000;
  requires 0 < pat_count < 1000000;
  requires hay_len == 0 || \valid_read(haystack + (0 .. hay_len - 1));
  requires \valid_read(patterns + (0 .. pat_count - 1));
  requires \valid_read(pat_lens + (0 .. pat_count - 1));
  requires well_formed_patterns(patterns, pat_lens, pat_count);
  requires 0 <= max_results;
  requires max_results == 0 ||
           (\valid(out_pids + (0 .. max_results - 1)) &&
            \valid(out_idxs + (0 .. max_results - 1)));
  assigns out_pids[0 .. max_results - 1], out_idxs[0 .. max_results - 1];
  ensures 0 <= \result <= max_results;
  ensures \forall integer k;
            0 <= k < \result ==>
              0 <= out_pids[k] < pat_count &&
              matches_at(haystack, hay_len,
                         patterns[out_pids[k]], pat_lens[out_pids[k]],
                         out_idxs[k]);
  ensures \forall integer pid, idx;
            0 <= pid < pat_count &&
            matches_at(haystack, hay_len, patterns[pid], pat_lens[pid], idx) ==>
              \exists integer k;
                0 <= k < \result &&
                out_pids[k] == pid &&
                out_idxs[k] == idx;
*/
int ac_automata_search(const unsigned char *haystack,
                       int hay_len,
                       const unsigned char * const *patterns,
                       const int *pat_lens,
                       int pat_count,
                       int *out_pids,
                       int *out_idxs,
                       int max_results) {
  // Implement and verify ac_automata_search here.
}
