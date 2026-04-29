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
  // Verus: fn flip_colors(node: Box<Node>) -> (res: Box<Node>)
  requires \valid_read(t);
  // node.left.is_some() && node.right.is_some()
  requires t->left  != \null;
  requires t->right != \null;
  requires \valid_read(t->left);
  requires \valid_read(t->right);
  // node.is_red != node.left.is_red
  requires t->is_red != t->left->is_red;
  // node.left.is_red == node.right.is_red
  requires t->left->is_red == t->right->is_red;
  assigns \nothing;
  ensures \result != \null;
  // res.view() =~= node.view()
  ensures \forall integer x; in_view(\result, x) <==> in_view{Pre}(t, x);
  ensures is_bst(\result);
  // Preservation of balance
  ensures black_height(\result) == \at(black_height(t), Pre);
  ensures \result->left  != \null;
  ensures \result->right != \null;
  // Toggles
  ensures \result->is_red != \at(t->is_red, Pre);
  ensures \result->left->is_red  != \at(t->left->is_red,  Pre);
  ensures \result->right->is_red != \at(t->right->is_red, Pre);
*/
LlrbtNode *llrbt_flipcolor(LlrbtNode *t) {
  // Implement and verify llrbt_flipcolor here.
}
