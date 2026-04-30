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
  // Verus: fn fixup_rotate_right(node: Box<Node>) -> (res: Box<Node>)
  requires \valid_read(t);
  requires is_bst(t);
  // node.left.is_some() && node.left.is_red
  requires t->left != \null;
  requires \valid_read(t->left);
  requires t->left->is_red;
  // Verus's `Box<Node>` consumes the input and returns a possibly-rebuilt
  // box; in C this is most naturally an in-place pointer rotation that
  // reuses the existing nodes. The original `assigns \nothing` cannot
  // model this. We mutate t (becomes new right child) and
  // \at(t->left, Pre) (becomes new root).
  assigns t->left, t->is_red,
          \at(t->left, Pre)->right, \at(t->left, Pre)->is_red;
  ensures \result != \null;
  ensures is_bst(\result);
  // res.view() =~= node.view()
  ensures \forall integer x; in_view(\result, x) <==> in_view{Pre}(t, x);
  ensures black_height(\result) == \at(black_height(t), Pre);
  ensures \result->is_red == \at(t->is_red, Pre);
  // 1. Structural Guarantee: old node becomes new right child
  ensures \result->right != \null;
  // 2. Safe Access: new right is red
  ensures \result->right->is_red;
*/
LlrbtNode *llrbt_rotateright(LlrbtNode *t) {
  // Implement and verify llrbt_rotateright here.
}
