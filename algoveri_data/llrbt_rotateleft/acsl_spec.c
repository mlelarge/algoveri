#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// Verus: pub struct Node { val: u64, is_red: bool, left/right: Option<Box<Node>> }
typedef struct LlrbtNode {
  uint64_t val;
  bool is_red;
  struct LlrbtNode *left;
  struct LlrbtNode *right;
} LlrbtNode;

/*@
  // Verus: pub open spec fn view(&self) -> Set<u64>
  predicate in_view{L}(LlrbtNode *t, integer x) =
    \valid_read(t) &&
    (t->val == x ||
     (t->left  != \null && in_view(t->left,  x)) ||
     (t->right != \null && in_view(t->right, x)));

  // Verus: pub open spec fn is_bst(&self) -> bool  decreases self
  predicate is_bst{L}(LlrbtNode *t) =
    \valid_read(t) &&
    (t->left == \null ||
       (is_bst(t->left)  &&
        \forall integer y; in_view(t->left, y) ==> y < t->val)) &&
    (t->right == \null ||
       (is_bst(t->right) &&
        \forall integer y; in_view(t->right, y) ==> y > t->val));

  axiomatic LlrbtBlackHeight {
    // Verus: pub open spec fn black_height(&self) -> int  decreases self
    logic integer black_height{L}(LlrbtNode *t)
      reads t, t->is_red, t->left, t->right;

    axiom black_height_def{L}:
      \forall LlrbtNode *t; \valid_read(t) ==>
        black_height(t) ==
          (\let lh = (t->left  == \null ? 1 : black_height(t->left));
           \let rh = (t->right == \null ? 1 : black_height(t->right));
           (lh != -1 && rh != -1 && lh == rh)
             ? (t->is_red ? lh : lh + 1)
             : -1);
  }
*/

/*@
  // Verus: fn fixup_rotate_left(node: Box<Node>) -> (res: Box<Node>)
  requires \valid_read(t);
  requires is_bst(t);
  // node.right.is_some() && node.right.is_red
  requires t->right != \null;
  requires \valid_read(t->right);
  requires t->right->is_red;
  // Verus's `Box<Node>` consumes the input and returns a possibly-rebuilt
  // box; in C this is most naturally an in-place pointer rotation that
  // reuses the existing nodes. The original `assigns \nothing` cannot
  // model this. We mutate t (becomes new left child) and \at(t->right, Pre)
  // (becomes new root).
  assigns t->right, t->is_red,
          \at(t->right, Pre)->left, \at(t->right, Pre)->is_red;
  // Structural
  ensures \result != \null;
  ensures is_bst(\result);
  // res.view() =~= node.view()
  ensures \forall integer x; in_view(\result, x) <==> in_view{Pre}(t, x);
  // 1. Structural Guarantee: old node becomes new left child
  ensures \result->left != \null;
  // Colors & Balance
  ensures black_height(\result) == \at(black_height(t), Pre);
  ensures \result->is_red == \at(t->is_red, Pre);
  // 2. Safe Access: new left is red
  ensures \result->left->is_red;
*/
LlrbtNode *llrbt_rotateleft(LlrbtNode *t) {
  // Implement and verify llrbt_rotateleft here.
}
