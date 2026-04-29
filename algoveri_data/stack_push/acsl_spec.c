#include <stdint.h>
#include <stddef.h>

// Verus: VerifiableStack<T>::push(&mut self, value: T)
//   ensures self.view() == old(self).view().push(value)
// In C the stack is represented as (data, len, cap) with data[0..*len) the view.

/*@
  requires \valid(len);
  requires 0 <= *len < cap;
  requires \valid(data + (0 .. cap - 1));
  assigns data[*len], *len;
  ensures *len == \old(*len) + 1;
  ensures \forall integer i; 0 <= i < \old(*len) ==> data[i] == \at(data[i], Pre);
  ensures data[\old(*len)] == value;
*/
void stack_push(int32_t *data, size_t *len, size_t cap, int32_t value) {
  // Implement and verify stack_push here.
}
