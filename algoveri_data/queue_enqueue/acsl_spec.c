#include <stdint.h>
#include <stddef.h>

// Verus: VerifiableQueue<T>::enqueue(&mut self, value: T)
//   ensures self.view() == old(self).view().push(value)
// In C the queue is represented as (data, len, cap) with data[0..*len) the view;
// enqueue appends at the back (data[*len]).

/*@
  requires \valid(len);
  requires 0 <= *len < cap;
  requires \valid(data + (0 .. cap - 1));
  // Verus's &mut self gives field-disjointness for free; in ACSL it must be stated.
  requires \separated(data + (0 .. cap - 1), len);
  assigns data[*len], *len;
  ensures *len == \old(*len) + 1;
  ensures \forall integer i; 0 <= i < \old(*len) ==> data[i] == \at(data[i], Pre);
  ensures data[\old(*len)] == value;
*/
void queue_enqueue(int32_t *data, size_t *len, size_t cap, int32_t value) {
  // Implement and verify queue_enqueue here.
}
