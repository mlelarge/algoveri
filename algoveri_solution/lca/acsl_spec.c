#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// Verus: pub struct Node { val: u64, left: Option<Box<Node>>, right: Option<Box<Node>> }
typedef struct TreeNode {
  uint64_t val;
  struct TreeNode *left;
  struct TreeNode *right;
} TreeNode;

/*@
  // Verus: pub open spec fn view(&self) -> Set<u64>
  // Set membership in the tree rooted at t.
  predicate in_view{L}(TreeNode *t, integer x) =
    \valid_read(t) &&
    (t->val == x ||
     (t->left  != \null && in_view(t->left,  x)) ||
     (t->right != \null && in_view(t->right, x)));

  // Verus: pub open spec fn contains(&self, target: u64) -> bool  decreases self
  predicate node_contains{L}(TreeNode *t, integer target) =
    \valid_read(t) &&
    (t->val == target ||
     (t->left  != \null && node_contains(t->left,  target)) ||
     (t->right != \null && node_contains(t->right, target)));

  // Verus: pub open spec fn tree_contains(root: Option<Box<Node>>, target: u64) -> bool
  predicate tree_contains{L}(TreeNode *t, integer target) =
    t != \null && node_contains(t, target);

  // Verus: pub open spec fn tree_distinct(root: Option<Box<Node>>) -> bool  decreases root
  predicate tree_distinct{L}(TreeNode *t) =
    t == \null ||
    (\valid_read(t) &&
     tree_distinct(t->left) &&
     tree_distinct(t->right) &&
     (t->left  == \null || !node_contains(t->left,  t->val)) &&
     (t->right == \null || !node_contains(t->right, t->val)) &&
     (t->left  == \null || t->right == \null ||
        \forall integer y;
          node_contains(t->left, y) ==> !node_contains(t->right, y)));

  axiomatic LcaSpec {
    // Verus: pub open spec fn spec_get_subtree(root, target) -> Option<Box<Node>>
    // Returns the subtree whose root has value `target`, or null if absent.
    // Defined recursively over the tree shape.
    logic TreeNode *spec_get_subtree{L}(TreeNode *t, integer target)
      reads t, t->val, t->left, t->right;

    axiom spec_get_subtree_null{L}:
      \forall integer target;
        spec_get_subtree(\null, target) == \null;

    axiom spec_get_subtree_node{L}:
      \forall TreeNode *t, integer target;
        \valid_read(t) ==>
          spec_get_subtree(t, target) ==
            (t->val == target
              ? t
              : (\let ls = spec_get_subtree(t->left,  target);
                 ls != \null
                   ? ls
                   : spec_get_subtree(t->right, target)));

    // Verus: pub open spec fn spec_get_depth(root, target) -> Option<int>
    // The depth of the node with value `target`. -1 if absent.
    logic integer spec_get_depth{L}(TreeNode *t, integer target)
      reads t, t->val, t->left, t->right;

    axiom spec_get_depth_null{L}:
      \forall integer target;
        spec_get_depth(\null, target) == -1;

    axiom spec_get_depth_node{L}:
      \forall TreeNode *t, integer target;
        \valid_read(t) ==>
          spec_get_depth(t, target) ==
            (t->val == target
              ? 0
              : (\let ld = spec_get_depth(t->left,  target);
                 \let rd = spec_get_depth(t->right, target);
                 ld != -1 ? ld + 1 : (rd != -1 ? rd + 1 : -1)));
  }

  // Verus: pub open spec fn is_common_ancestor(root, anc_val, p, q) -> bool
  predicate is_common_ancestor{L}(TreeNode *root, integer anc_val, integer p, integer q) =
    \let sub = spec_get_subtree(root, anc_val);
    sub != \null && node_contains(sub, p) && node_contains(sub, q);
*/

/*@
  // Verus: fn lowest_common_ancestor(root: &Option<Box<Node>>, p: u64, q: u64) -> (res: Option<u64>)
  requires tree_contains(root, p);
  requires tree_contains(root, q);
  requires tree_distinct(root);
  assigns \nothing;
  // res.is_some() && is_common_ancestor(*root, res.get_Some_0(), p, q)
  ensures is_common_ancestor(root, \result, p, q);
  // forall x. is_common_ancestor(*root, x, p, q) ==>
  //   spec_get_depth(*root, x) <= spec_get_depth(*root, res)
  ensures \forall integer x;
    is_common_ancestor(root, x, p, q) ==>
      spec_get_depth(root, x) <= spec_get_depth(root, \result);
*/
uint64_t lca(const TreeNode *root, uint64_t p, uint64_t q) {
  // Implement and verify lca here.
}
