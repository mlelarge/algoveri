#include <stddef.h>
#include <stdbool.h>

// Verus: pub struct Node { val: u8, is_end: bool, left/mid/right: Option<Box<Node>> }
typedef struct TstNode {
  unsigned char val;
  bool is_end;
  struct TstNode *left;
  struct TstNode *mid;
  struct TstNode *right;
} TstNode;

/*@
  // Verus: spec fn contains(&self, key: Seq<u8>) -> bool  decreases self
  // Empty keys are never present in this encoding.
  predicate tst_contains{L}(TstNode *t, unsigned char *key, integer len) =
    \valid_read(t) &&
    len > 0 &&
    \valid_read(key + (0 .. len - 1)) &&
    ((key[0] <  t->val && t->left  != \null && tst_contains(t->left,  key, len)) ||
     (key[0] >  t->val && t->right != \null && tst_contains(t->right, key, len)) ||
     (key[0] == t->val &&
       ((len == 1 && t->is_end) ||
        (len >  1 && t->mid != \null &&
                     tst_contains(t->mid, key + 1, len - 1)))));

  // Verus: spec fn is_empty(&self) -> bool
  predicate tst_is_empty{L}(TstNode *t) =
    \valid_read(t) && !t->is_end &&
    t->left == \null && t->mid == \null && t->right == \null;

  // Verus: pub open spec fn well_formed(&self) -> bool  decreases self
  // Structural recursion + pruning + BST invariant on left/right.
  predicate well_formed{L}(TstNode *t) =
    \valid_read(t) &&
    (t->left == \null ||
       (well_formed(t->left) && !tst_is_empty(t->left) &&
        \forall unsigned char *s, integer sl;
          tst_contains(t->left, s, sl) ==> sl > 0 && s[0] < t->val)) &&
    (t->right == \null ||
       (well_formed(t->right) && !tst_is_empty(t->right) &&
        \forall unsigned char *s, integer sl;
          tst_contains(t->right, s, sl) ==> sl > 0 && s[0] > t->val)) &&
    (t->mid == \null ||
       (well_formed(t->mid) && !tst_is_empty(t->mid)));

  // Verus: opt_well_formed
  predicate opt_well_formed{L}(TstNode *t) =
    t == \null || (\valid_read(t) && well_formed(t) && !tst_is_empty(t));

  // Verus: opt_view(node).contains(key) — true iff key is in opt_view of node.
  predicate opt_contains{L}(TstNode *t, unsigned char *key, integer len) =
    t != \null && tst_contains(t, key, len);
*/

/*@
  // Verus: fn search(tree: Option<Box<Node>>, key: Seq<u8>) -> (res: bool)
  requires opt_well_formed(t);
  requires len >= 0;
  requires len == 0 || \valid_read(key + (0 .. len - 1));
  assigns \nothing;
  ensures (\result != 0) <==> opt_contains(t, (unsigned char *)key, len);
*/
bool tst_search(const TstNode *t, const unsigned char *key, size_t len) {
  // Implement and verify tst_search here.
}
