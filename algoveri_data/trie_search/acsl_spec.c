#include <stddef.h>
#include <stdbool.h>

// Verus: pub struct Node { is_end: bool, children: Vec<Option<Box<Node>>> }
// Verus enforces children.len() == 256.
typedef struct TrieNode {
  bool is_end;
  struct TrieNode *children[256];
} TrieNode;

/*@
  // Verus: spec fn contains(&self, key: Seq<u8>) -> bool  decreases key.len()
  predicate trie_contains{L}(TrieNode *t, unsigned char *key, integer len) =
    \valid_read(t) &&
    ((len == 0 && t->is_end) ||
     (len > 0 && \valid_read(key + (0 .. len - 1)) &&
      t->children[key[0]] != \null &&
      trie_contains(t->children[key[0]], key + 1, len - 1)));

  // Verus: spec fn is_empty(&self) -> bool
  predicate trie_is_empty{L}(TrieNode *t) =
    \valid_read(t) && !t->is_end &&
    \forall integer i; 0 <= i < 256 ==> t->children[i] == \null;

  // Verus: pub open spec fn well_formed(&self) -> bool  decreases self
  // Each existing child is well-formed and not "empty" (pruning invariant).
  predicate well_formed{L}(TrieNode *t) =
    \valid_read(t) &&
    \forall integer i; 0 <= i < 256 ==>
      (t->children[i] == \null ||
       (well_formed(t->children[i]) && !trie_is_empty(t->children[i])));

  predicate opt_well_formed{L}(TrieNode *t) =
    t == \null || (\valid_read(t) && well_formed(t) && !trie_is_empty(t));

  predicate opt_contains{L}(TrieNode *t, unsigned char *key, integer len) =
    t != \null && trie_contains(t, key, len);
*/

/*@
  // Verus: fn search(tree: Option<Box<Node>>, key: Seq<u8>) -> (res: bool)
  requires opt_well_formed(t);
  requires len >= 0;
  requires len == 0 || \valid_read(key + (0 .. len - 1));
  assigns \nothing;
  ensures (\result != 0) <==> opt_contains(t, (unsigned char *)key, len);
*/
bool trie_search(const TrieNode *t, const unsigned char *key, size_t len) {
  // Implement and verify trie_search here.
}
