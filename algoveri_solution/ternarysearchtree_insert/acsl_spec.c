#include <stddef.h>
#include <stdbool.h>

typedef struct TstNode {
  unsigned char val;
  bool is_end;
  struct TstNode *left;
  struct TstNode *mid;
  struct TstNode *right;
} TstNode;

/*@
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

  predicate tst_is_empty{L}(TstNode *t) =
    \valid_read(t) && !t->is_end &&
    t->left == \null && t->mid == \null && t->right == \null;

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

  predicate opt_well_formed{L}(TstNode *t) =
    t == \null || (\valid_read(t) && well_formed(t) && !tst_is_empty(t));

  predicate opt_contains{L}(TstNode *t, unsigned char *key, integer len) =
    t != \null && tst_contains(t, key, len);

  predicate seq_eq{L}(unsigned char *a, integer la, unsigned char *b, integer lb) =
    la == lb && \forall integer i; 0 <= i < la ==> a[i] == b[i];
*/

/*@
  // Verus: fn insert(tree: Option<Box<Node>>, key: Seq<u8>) -> (res: Box<Node>)
  // Verus precondition: key.len() > 0
  requires opt_well_formed(t);
  requires len > 0;
  requires \valid_read(key + (0 .. len - 1));
  assigns \nothing;
  allocates \result;
  ensures \result != \null;
  ensures well_formed(\result);
  ensures !tst_is_empty(\result);
  // The inserted key is now present.
  ensures tst_contains(\result, (unsigned char *)key, len);
  // Frame: every other key has the same membership as before.
  ensures \forall unsigned char *k, integer kl;
    !seq_eq(k, kl, (unsigned char *)key, len) ==>
      (tst_contains(\result, k, kl) <==> opt_contains{Pre}(t, k, kl));
*/
TstNode *tst_insert(TstNode *t, const unsigned char *key, size_t len) {
  // Implement and verify tst_insert here.
}
