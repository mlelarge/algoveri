#include <stdint.h>
#include <stddef.h>

/*@
  // Verus: spec fn max(a: int, b: int) -> int
  logic integer max2(integer a, integer b) = (a > b) ? a : b;

  // Verus: spec fn lcs_spec(s1: Seq<char>, s2: Seq<char>) -> int
  //   decreases s1.len(), s2.len()
  //   if s1 or s2 empty -> 0;
  //   else if s1[n-1] == s2[m-1] -> 1 + lcs_spec(s1[0..n-1], s2[0..m-1]);
  //   else max(lcs_spec(s1[0..n-1], s2), lcs_spec(s1, s2[0..m-1])).
  axiomatic LcsSpec {
    logic integer lcs_spec{L}(unsigned char *s, integer n,
                              unsigned char *t, integer m)
      reads s[0 .. n - 1], t[0 .. m - 1];

    axiom lcs_spec_base{L}:
      \forall unsigned char *s, integer n, unsigned char *t, integer m;
        (n <= 0 || m <= 0) ==> lcs_spec(s, n, t, m) == 0;

    axiom lcs_spec_match{L}:
      \forall unsigned char *s, integer n, unsigned char *t, integer m;
        n > 0 && m > 0 && s[n - 1] == t[m - 1] ==>
          lcs_spec(s, n, t, m) == 1 + lcs_spec(s, n - 1, t, m - 1);

    axiom lcs_spec_mismatch{L}:
      \forall unsigned char *s, integer n, unsigned char *t, integer m;
        n > 0 && m > 0 && s[n - 1] != t[m - 1] ==>
          lcs_spec(s, n, t, m) ==
            max2(lcs_spec(s, n - 1, t, m), lcs_spec(s, n, t, m - 1));
  }
*/


/*@
  // Verus: fn solve_longest_common_subsequence(input: &Input) -> (len: usize)
  //   requires input.s.len() <= 3000, input.t.len() <= 3000
  //   ensures len as int == lcs_spec(input.s@, input.t@).
  // C: input.s/input.t passed as (s, n) / (t, m) parallel slices.
  requires 0 <= n <= 3000;
  requires 0 <= m <= 3000;
  requires n == 0 || \valid_read(s + (0 .. n - 1));
  requires m == 0 || \valid_read(t + (0 .. m - 1));
  assigns \nothing;
  ensures \result == lcs_spec((unsigned char *)s, n, (unsigned char *)t, m);
*/
int solve_longest_common_subsequence(const unsigned char *s, int n,
                                     const unsigned char *t, int m) {
  // Implement and verify solve_longest_common_subsequence here.
}
