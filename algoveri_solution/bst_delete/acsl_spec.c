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

  predicate opt_is_bst{L}(BstNode *t) =
    t == \null || is_bst(t);
*/

/*@
  // Verus: fn delete(tree: Option<Box<Node>>, v: u64) -> (res: Option<Box<Node>>)
  requires opt_is_bst(t);
  assigns \nothing;
  // If the result is non-null: it is a valid BST whose view = old view minus v.
  ensures \result != \null ==>
    is_bst(\result) &&
    (\forall integer x;
       in_view(\result, x) <==> (t != \null && in_view{Pre}(t, x) && x != v));
  // If the result is null: the old tree was empty, or contained only v.
  ensures \result == \null ==>
    (t == \null ||
     (\forall integer x; in_view{Pre}(t, x) ==> x == v));
*/
BstNode *bst_delete(BstNode *t, uint64_t v) {
  // Implement and verify bst_delete here.
}
