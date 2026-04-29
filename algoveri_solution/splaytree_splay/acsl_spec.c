#include <stddef.h>
#include <stdint.h>

// Verus: pub struct Node { val: u64, left/right: Option<Box<Node>> }
typedef struct SplayNode {
  uint64_t val;
  struct SplayNode *left;
  struct SplayNode *right;
} SplayNode;

/*@
  // Verus: pub open spec fn view(&self) -> Set<u64>
  // Membership in the BST rooted at t (recursive).
  predicate in_view{L}(SplayNode *t, integer x) =
    \valid_read(t) &&
    (t->val == x ||
     (t->left  != \null && in_view(t->left,  x)) ||
     (t->right != \null && in_view(t->right, x)));

  // Verus: pub open spec fn is_bst(&self) -> bool
  predicate is_bst{L}(SplayNode *t) =
    \valid_read(t) &&
    (t->left == \null ||
       (is_bst(t->left)  &&
        \forall integer y; in_view(t->left, y) ==> y < t->val)) &&
    (t->right == \null ||
       (is_bst(t->right) &&
        \forall integer y; in_view(t->right, y) ==> y > t->val));
*/

/*@
  // Verus: fn splay(tree: Box<Node>, v: u64) -> (res: Box<Node>)
  requires \valid(t);
  requires is_bst(t);
  assigns \nothing;
  ensures \valid(\result);
  ensures is_bst(\result);
  // The key set is preserved.
  ensures \forall integer x; in_view(\result, x) <==> in_view{Pre}(t, x);
  // If v was present, it is now at the root.
  ensures in_view{Pre}(t, v) ==> \result->val == v;
  // If v was absent, the new root is some element of the tree.
  ensures !in_view{Pre}(t, v) ==> in_view(\result, \result->val);
*/
SplayNode *splay(SplayNode *t, uint64_t v) {
  // Implement and verify splay here.
}
