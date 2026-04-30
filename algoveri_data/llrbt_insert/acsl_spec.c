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
  // Membership in the set of values stored in the LLRBT rooted at t.
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
  // No right-leaning red, and no double red on the left.
  predicate satisfies_red_props{L}(LlrbtNode *t) =
    \valid_read(t) &&
    (t->left  == \null || satisfies_red_props(t->left)) &&
    (t->right == \null || satisfies_red_props(t->right)) &&
    (t->right == \null || !t->right->is_red) &&
    (t->left  == \null || !t->left->is_red ||
       t->left->left == \null || !t->left->left->is_red);

  axiomatic LlrbtBlackHeight {
    // Verus: pub open spec fn black_height(&self) -> int  decreases self
    // Returns -1 if invalid (left/right black-heights disagree). Otherwise:
    // it is lh + 1 if t is black, or lh if t is red, where lh is the common
    // child height (1 for null children).
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
  // Verus: fn insert(tree: Option<Box<Node>>, v: u64) -> (res: Box<Node>)
  requires opt_is_llrbt(t);
  // Verus's `Box<Node>` consumes the input tree and returns a (possibly
  // freshly built) box. A correct C implementation must either allocate
  // a new node (when t is null) or mutate/rebuild the existing tree.
  // The original `assigns \nothing` makes every real implementation
  // unprovable. We keep the assigns empty for memory locations but
  // allow fresh allocation of the result.
  assigns \nothing;
  allocates \result;
  ensures \result != \null;
  ensures is_llrbt(\result);
  // res.view() =~= match tree { Some(n) => n.view().insert(v), None => Set::empty().insert(v) }
  ensures \forall integer x;
    in_view(\result, x) <==> (x == v || (t != \null && in_view{Pre}(t, x)));
*/
LlrbtNode *llrbt_insert(LlrbtNode *t, uint64_t v) {
  // Implement and verify llrbt_insert here.
}
