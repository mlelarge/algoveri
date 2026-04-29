#include <stdint.h>
#include <stddef.h>

// Verus: RingBuffer<T>::enqueue(&mut self, value: T) -- "enqueue with overwrite".
//   ensures
//     old.len <  capacity ==> self.view() == old.view().push(value)
//     old.len == capacity ==> self.view() == old.view().drop_first().push(value)
// In C the ringbuffer is represented as (data, head, len, cap); the live view is
// data[(*head + i) % cap] for 0 <= i < *len.

/*@
  requires 0 < cap <= 1024;
  requires \valid(data + (0 .. cap - 1));
  requires \valid(head);
  requires \valid(len);
  requires 0 <= *head < cap;
  requires 0 <= *len <= cap;
  assigns data[0 .. cap - 1], *head, *len;
  ensures \at(*len,Pre) < cap ==> *len == \at(*len,Pre) + 1;
  ensures \at(*len,Pre) == cap ==> *len == cap;
  ensures \at(*len,Pre) < cap ==> *head == \at(*head,Pre);
  ensures \at(*len,Pre) == cap ==> *head == (\at(*head,Pre) + 1) % cap;
*/
void ringbuffer_enqueue(int32_t *data, size_t *head, size_t *len, size_t cap, int32_t value) {
  // Implement and verify ringbuffer_enqueue here.
}
