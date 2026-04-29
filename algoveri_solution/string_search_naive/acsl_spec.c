#include <stdint.h>

/*@
  predicate matches_at{L}(unsigned char *hay, integer hay_len,
                         unsigned char *needle, integer needle_len,
                         integer start) =
    0 <= start &&
    start + needle_len <= hay_len &&
    (\forall integer i; 0 <= i < needle_len ==> hay[start + i] == needle[i]);
*/


/*@
  requires 0 <= hay_len <= 1000000;
  requires 0 <= needle_len <= 1000000;
  requires \valid_read(hay + (0 .. hay_len - 1));
  requires \valid_read(needle + (0 .. needle_len - 1));
  requires \valid(out_len);
  requires needle_len == 0 ==> \valid(out + (0 .. hay_len));
  requires needle_len > 0 ==> \valid(out + (0 .. hay_len - needle_len));
  assigns out[0 .. hay_len], *out_len;
  ensures 0 <= *out_len <= hay_len + 1;
  ensures \forall integer i; 0 <= i < *out_len ==> matches_at((unsigned char *)hay, hay_len, (unsigned char *)needle, needle_len, out[i]);
  ensures \forall integer i; matches_at((unsigned char *)hay, hay_len, (unsigned char *)needle, needle_len, i) ==> (\exists integer k; 0 <= k < *out_len && out[k] == i);
*/
void naive_search(const unsigned char *hay, int hay_len,
                  const unsigned char *needle, int needle_len,
                  int *out, int *out_len) {
  // Implement and verify naive_search here.
}
