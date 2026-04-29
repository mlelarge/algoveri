#include <stdint.h>
#include <stddef.h>

// Verus: VerifiableStack<T>::pop(&mut self) -> T
//   requires old(self).view().len() > 0
//   ensures val == old(self).view().last(),
//           self.view() == old(self).view().drop_last()
// In C the stack is represented as (data, len, cap) with data[0..*len) the view.

/*@
  requires \valid(len);
  requires 0 < *len <= cap;
  requires \valid(data + (0 .. cap - 1));
  assigns *len;
  ensures *len == \old(*len) - 1;
  ensures \result == \at(data[\old(*len) - 1], Pre);
  ensures \forall integer i; 0 <= i < *len ==> data[i] == \at(data[i], Pre);
*/
int32_t stack_pop(int32_t *data, size_t *len, size_t cap) {
  // Implement and verify stack_pop here.
}
