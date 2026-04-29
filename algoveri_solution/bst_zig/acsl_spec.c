#include <stddef.h>
#include <stdint.h>

// Verus: pub struct Node { val: u64, left: Option<Box<Node>>, right: Option<Box<Node>> }
typedef struct BstNode {
  uint64_t val;
  struct BstNode *left;
  struct BstNode *right;
} BstNode;

/*@
  // Verus: pub open spec fn view(&self) -> Set<u64>
  // Membership in the set of values stored in the BST rooted at t.
  predicate in_view{L}(BstNode *t, integer x) =
    \valid_read(t) &&
    (t->val == x ||
     (t->left  != \null && in_view(t->left,  x)) ||
     (t->right != \null && in_view(t->right, x)));

  // Verus: pub open spec fn is_bst(&self) -> bool  decreases self
  predicate is_bst{L}(BstNode *t) =
    \valid_read(t) &&
    (t->left == \null ||
       (is_bst(t->left)  &&
        \forall integer y; in_view(t->left, y) ==> y < t->val)) &&
    (t->right == \null ||
       (is_bst(t->right) &&
        \forall integer y; in_view(t->right, y) ==> y > t->val));
*/

/*@
  // Verus: fn zig(node: Box<Node>) -> (res: Box<Node>)
  requires \valid_read(t);
  requires is_bst(t);
  // Zig requires a left child.
  requires t->left != \null;
  assigns \nothing;
  ensures \result != \null;
  ensures is_bst(\result);
  // res.view() =~= node.view()
  ensures \forall integer x; in_view(\result, x) <==> in_view{Pre}(t, x);
  // res.val == node.left.val (left child becomes root)
  ensures \result->val == \at(t->left->val, Pre);
  // res.right.is_some() && res.right.val == node.val (old root becomes right child)
  ensures \result->right != \null;
  ensures \result->right->val == \at(t->val, Pre);
*/
BstNode *bst_zig(BstNode *t) {
  // Implement and verify bst_zig here.
}
