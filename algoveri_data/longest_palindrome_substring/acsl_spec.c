#include <stdint.h>
#include <stddef.h>

/*@
  // Verus: pub open spec fn is_valid_subrange(s: Seq<u8>, start: int, len: int) -> bool
  predicate valid_subrange(integer n, integer start, integer len) =
    0 <= start && 0 <= len && start + len <= n;

  // Verus: pub open spec fn is_palindrome(s: Seq<u8>) -> bool
  //   forall i in [0, len), s[i] == s[len - 1 - i].
  // Lifted to a substring: palindrome_range(s, n, start, len) iff
  //   valid_subrange(n, start, len) && is_palindrome(s[start .. start+len)).
  predicate palindrome_range{L}(unsigned char *s, integer n,
                                integer start, integer len) =
    valid_subrange(n, start, len) &&
    (\forall integer i; 0 <= i < len ==>
       s[start + i] == s[start + len - 1 - i]);
*/


/*@
  // Verus: fn longest_palindromic_substring(s: Seq<u8>) -> (res: (usize, usize))
  //   requires s.len() <= 1_000_000
  //   ensures is_valid_subrange(s, res.0, res.1),
  //           is_palindrome(s.subrange(res.0, res.0 + res.1)),
  //           forall i, len. is_valid_subrange(s, i, len) &&
  //                          is_palindrome(s.subrange(i, i + len))
  //              ==> len <= res.1.
  requires 0 <= n <= 1000000;
  requires n == 0 || \valid_read(s + (0 .. n - 1));
  requires \valid(out_start);
  requires \valid(out_len);
  assigns *out_start, *out_len;
  ensures valid_subrange(n, *out_start, *out_len);
  ensures palindrome_range((unsigned char *)s, n, *out_start, *out_len);
  ensures \forall integer i, len;
            valid_subrange(n, i, len) &&
            palindrome_range((unsigned char *)s, n, i, len) ==> len <= *out_len;
*/
void longest_palindromic_substring(const unsigned char *s, int n,
                                   int *out_start, int *out_len) {
  // Implement and verify longest_palindromic_substring here.
}
