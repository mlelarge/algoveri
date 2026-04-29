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

  // Verus: pub open spec fn satisfies_red_props(&self) -> bool  decreases self
  predicate satisfies_red_props{L}(LlrbtNode *t) =
    \valid_read(t) &&
    (t->left  == \null || satisfies_red_props(t->left)) &&
    (t->right == \null || satisfies_red_props(t->right)) &&
    (t->right == \null || !t->right->is_red) &&
    (t->left  == \null || !t->left->is_red ||
       t->left->left == \null || !t->left->left->is_red);

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

  // Verus: pub open spec fn is_llrbt(&self) -> bool
  predicate is_llrbt{L}(LlrbtNode *t) =
    \valid_read(t) &&
    is_bst(t) &&
    black_height(t) != -1 &&
    satisfies_red_props(t);

  predicate opt_is_llrbt{L}(LlrbtNode *t) =
    t == \null || is_llrbt(t);
*/

/*@
  // Verus: fn delete(tree: Option<Box<Node>>, v: u64) -> (res: Option<Box<Node>>)
  requires opt_is_llrbt(t);
  assigns \nothing;
  // If the result is non-null: it is a valid LLRBT whose view = old view minus v.
  ensures \result != \null ==>
    is_llrbt(\result) &&
    (\forall integer x;
       in_view(\result, x) <==> (t != \null && in_view{Pre}(t, x) && x != v));
  // If the result is null: removing v from the old view yields the empty set.
  ensures \result == \null ==>
    (t == \null ||
     (\forall integer x; in_view{Pre}(t, x) ==> x == v));
*/
LlrbtNode *llrbt_delete(LlrbtNode *t, uint64_t v) {
  // Implement and verify llrbt_delete here.
}
