#include <stdint.h>

// Verus: pub struct BinaryMaxHeap { pub storage: Vec<u32>, pub len: usize }
// C: caller passes the storage array and a pointer to len.

/*@
  // Verus: spec fn is_heap(&self) -> bool
  //   self.len <= max_capacity() && self.len <= self.storage.len()
  //   && forall i. 1 <= i < self.len ==> storage[i] <= storage[(i-1)/2]
  predicate is_heap{L}(uint32_t *a, integer len) =
    0 <= len <= 1023 &&
    (\forall integer i; 1 <= i < len ==> a[i] <= a[(i - 1) / 2]);

  // Verus: spec fn view(&self) -> Multiset<u32>
  //   storage.view().take(self.len as int).to_multiset()
  axiomatic HeapMultiset {
    logic integer count_occ{L}(uint32_t *a, integer n, integer v)
      reads a[0 .. n - 1];

    axiom count_occ_base{L}:
      \forall uint32_t *a, integer v;
        count_occ(a, 0, v) == 0;

    axiom count_occ_step{L}:
      \forall uint32_t *a, integer n, integer v;
        n > 0 ==>
        count_occ(a, n, v) == count_occ(a, n - 1, v) + (a[n - 1] == v ? 1 : 0);
  }
*/

/*@
  // Verus: fn pop_max(heap: &mut BinaryMaxHeap) -> (max: u32)
  //   requires old.is_heap(), old.len > 0
  //   ensures  heap.is_heap()
  //         /\ heap.len == old.len - 1
  //         /\ forall x. old.view().contains(x) ==> max >= x
  //         /\ heap.view() =~= old.view().remove(max)
  requires \valid(len);
  requires \valid(a + (0 .. *len - 1));
  requires 0 < *len <= 1023;
  requires is_heap(a, *len);
  assigns a[0 .. *len - 1], *len;
  ensures *len == \old(*len) - 1;
  ensures is_heap(a, *len);
  // \result is at least every element of the original heap.
  ensures \forall integer x;
    count_occ{Pre}(a, \old(*len), x) > 0 ==> \result >= x;
  // The new view is the old view with one occurrence of \result removed.
  ensures \forall integer x;
    count_occ{Post}(a, *len, x) ==
      count_occ{Pre}(a, \old(*len), x) - (x == \result ? 1 : 0);
*/
uint32_t pop_max(uint32_t *a, int *len) {
  // Implement and verify pop_max here.
}
