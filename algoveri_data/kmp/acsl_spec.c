#include <stdint.h>
#include <stddef.h>

/*@
  // Verus: spec fn matches_at(haystack: Seq<u8>, needle: Seq<u8>, start_index: int) -> bool
  //   0 <= start_index && start_index + needle.len() <= haystack.len()
  //   && forall i in [0, needle.len()), haystack[start + i] == needle[i].
  predicate matches_at{L}(unsigned char *haystack, integer hay_len,
                          unsigned char *needle, integer needle_len,
                          integer start_index) =
    0 <= start_index &&
    start_index + needle_len <= hay_len &&
    (\forall integer i; 0 <= i < needle_len ==> haystack[start_index + i] == needle[i]);
*/


/*@
  // Verus: fn kmp_search(haystack: &Vec<u8>, needle: &Vec<u8>) -> (indices: Vec<usize>)
  //   requires haystack.len() < 1_000_000, needle.len() < 1_000_000
  //   ensures soundness: every returned index is a match,
  //           completeness: every match index appears in indices.
  requires 0 <= hay_len < 1000000;
  requires 0 <= needle_len < 1000000;
  requires \valid_read(haystack + (0 .. hay_len - 1));
  requires \valid_read(needle + (0 .. needle_len - 1));
  requires \valid(out_indices + (0 .. hay_len));
  requires \valid(out_len);
  assigns out_indices[0 .. hay_len], *out_len;
  ensures 0 <= *out_len <= hay_len + 1;
  ensures \forall integer i; 0 <= i < *out_len ==>
            matches_at((unsigned char *)haystack, hay_len,
                       (unsigned char *)needle, needle_len, out_indices[i]);
  ensures \forall integer i;
            matches_at((unsigned char *)haystack, hay_len,
                       (unsigned char *)needle, needle_len, i) ==>
            (\exists integer k; 0 <= k < *out_len && out_indices[k] == i);
*/
void kmp_search(const unsigned char *haystack, int hay_len,
                const unsigned char *needle, int needle_len,
                int *out_indices, int *out_len) {
  // Implement and verify kmp_search here.
}
