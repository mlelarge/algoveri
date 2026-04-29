#include <stdint.h>

// Verus: pub struct BinaryMaxHeap { pub storage: Vec<u32>, pub len: usize }
// C: caller passes the storage array, its physical capacity, and a pointer to len.
// max_capacity() == 1023 in the Verus model.

/*@
  // Verus: spec fn is_heap(&self) -> bool
  //   self.len <= max_capacity() && self.len <= self.storage.len()
  //   && forall i. 1 <= i < self.len ==> storage[i] <= storage[(i-1)/2]
  predicate is_heap{L}(uint32_t *a, integer len) =
    0 <= len <= 1023 &&
    (\forall integer i; 1 <= i < len ==> a[i] <= a[(i - 1) / 2]);

  // Verus: spec fn view(&self) -> Multiset<u32>
  //   storage.view().take(self.len as int).to_multiset()
  // ACSL: count occurrences of each value in the prefix a[0 .. n - 1].
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

  // Multiset equivalence corresponding to view{L2} == view{L1}.insert(v).
  predicate view_inserted{L1,L2}(uint32_t *a, integer n_old, integer v) =
    \forall integer x;
      count_occ{L2}(a, n_old + 1, x) ==
      count_occ{L1}(a, n_old, x) + (x == v ? 1 : 0);
*/

/*@
  // Verus: fn push(heap: &mut BinaryMaxHeap, v: u32)
  //   requires old.is_heap(), old.len < max_capacity(), old.storage.len() > old.len
  //   ensures  heap.is_heap()
  //         /\ heap.len == old.len + 1
  //         /\ heap.view() =~= old.view().insert(v)
  // C: a is the storage; len is the current size; capacity is the storage length.
  requires \valid(a + (0 .. capacity - 1));
  requires 0 <= len < 1023;
  requires len < capacity;
  requires is_heap(a, len);
  assigns a[0 .. len];
  ensures is_heap(a, len + 1);
  // The new element v is now somewhere in a[0 .. len], multiset-wise:
  ensures view_inserted{Pre,Post}(a, len, v);
*/
void maxheap_push(uint32_t *a, int len, int capacity, uint32_t v) {
  // Implement and verify maxheap_push here.
}
