#include <stddef.h>
#include <stdint.h>

// Verus: pub struct Node { val: u64, low: u64, high: u64, left/right: Option<Box<Node>> }
typedef struct SegNode {
  uint64_t val;
  uint64_t low;
  uint64_t high;
  struct SegNode *left;
  struct SegNode *right;
} SegNode;

/*@
  // Verus: pub open spec fn is_segment_tree(&self) -> bool  decreases self
  // ACSL recursive predicate (fixpoint). Termination is not formally checked
  // by Frama-C but is structurally well-founded.
  predicate is_segment_tree{L}(SegNode *t) =
    \valid(t) &&
    t->low < t->high &&
    (
      // Leaf case
      (t->left == \null && t->right == \null && t->high == t->low + 1) ||
      // Internal case
      (t->left != \null && t->right != \null &&
       t->left->low  == t->low &&
       t->left->high == (t->low + t->high) / 2 &&
       t->right->low == (t->low + t->high) / 2 &&
       t->right->high == t->high &&
       is_segment_tree(t->left) &&
       is_segment_tree(t->right) &&
       t->val == (t->left->val > t->right->val ? t->left->val : t->right->val))
    );

  // Membership in the index domain [t->low, t->high).
  predicate in_view{L}(SegNode *t, integer k) =
    \valid_read(t) && t->low <= k < t->high;

  axiomatic SegmentTreeView {
    // Verus: spec fn view(&self) -> Map<int, u64>
    // The value stored at index k. Defined recursively via the structural axioms.
    logic uint64_t view_at{L}(SegNode *t, integer k)
      reads t, t->val, t->low, t->high, t->left, t->right;

    axiom view_at_leaf{L}:
      \forall SegNode *t, integer k;
        \valid_read(t) && t->left == \null && t->right == \null && k == t->low ==>
          view_at(t, k) == t->val;

    axiom view_at_left{L}:
      \forall SegNode *t, integer k;
        \valid_read(t) && t->left != \null &&
        t->left->low <= k < t->left->high ==>
          view_at(t, k) == view_at(t->left, k);

    axiom view_at_right{L}:
      \forall SegNode *t, integer k;
        \valid_read(t) && t->right != \null &&
        t->right->low <= k < t->right->high ==>
          view_at(t, k) == view_at(t->right, k);
  }
*/

/*@
  // Verus: fn build(l: u64, r: u64) -> (res: Box<Node>)
  requires l < r;
  assigns \nothing;
  allocates \result;
  ensures \result != \null;
  ensures is_segment_tree(\result);
  ensures \result->low == l;
  ensures \result->high == r;
  // All values in [l, r) are initialized to 0.
  ensures \forall integer k; l <= k < r ==>
    in_view(\result, k) && view_at(\result, k) == 0;
*/
SegNode *seg_build(uint64_t l, uint64_t r) {
  // Implement and verify seg_build here.
}
