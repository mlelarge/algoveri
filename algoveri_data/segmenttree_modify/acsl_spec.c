#include <stddef.h>
#include <stdint.h>

typedef struct SegNode {
  uint64_t val;
  uint64_t low;
  uint64_t high;
  struct SegNode *left;
  struct SegNode *right;
} SegNode;

/*@
  predicate is_segment_tree{L}(SegNode *t) =
    \valid(t) &&
    t->low < t->high &&
    (
      (t->left == \null && t->right == \null && t->high == t->low + 1) ||
      (t->left != \null && t->right != \null &&
       t->left->low  == t->low &&
       t->left->high == (t->low + t->high) / 2 &&
       t->right->low == (t->low + t->high) / 2 &&
       t->right->high == t->high &&
       is_segment_tree(t->left) &&
       is_segment_tree(t->right) &&
       t->val == (t->left->val > t->right->val ? t->left->val : t->right->val))
    );

  predicate in_view{L}(SegNode *t, integer k) =
    \valid_read(t) && t->low <= k < t->high;

  axiomatic SegmentTreeView {
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
  // Verus: fn modify(node: Box<Node>, idx: u64, v: u64) -> (res: Box<Node>)
  requires \valid(t);
  requires is_segment_tree(t);
  requires t->low <= idx < t->high;
  assigns \nothing;
  allocates \result;
  ensures \result != \null;
  ensures is_segment_tree(\result);
  ensures \result->low == \at(t->low, Pre);
  ensures \result->high == \at(t->high, Pre);
  // Verus: res.view() =~= node.view().insert(idx as int, v)
  ensures \forall integer k;
    \at(t->low, Pre) <= k < \at(t->high, Pre) ==>
      in_view(\result, k) &&
      view_at(\result, k) == (k == idx ? v : view_at{Pre}(t, k));
*/
SegNode *seg_modify(SegNode *t, uint64_t idx, uint64_t v) {
  // Implement and verify seg_modify here.
}
