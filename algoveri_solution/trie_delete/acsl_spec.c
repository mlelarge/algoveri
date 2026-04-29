#include <stddef.h>
#include <stdbool.h>

typedef struct TrieNode {
  bool is_end;
  struct TrieNode *children[256];
} TrieNode;

/*@
  predicate trie_contains{L}(TrieNode *t, unsigned char *key, integer len) =
    \valid_read(t) &&
    ((len == 0 && t->is_end) ||
     (len > 0 && \valid_read(key + (0 .. len - 1)) &&
      t->children[key[0]] != \null &&
      trie_contains(t->children[key[0]], key + 1, len - 1)));

  predicate trie_is_empty{L}(TrieNode *t) =
    \valid_read(t) && !t->is_end &&
    \forall integer i; 0 <= i < 256 ==> t->children[i] == \null;

  predicate well_formed{L}(TrieNode *t) =
    \valid_read(t) &&
    \forall integer i; 0 <= i < 256 ==>
      (t->children[i] == \null ||
       (well_formed(t->children[i]) && !trie_is_empty(t->children[i])));

  predicate opt_well_formed{L}(TrieNode *t) =
    t == \null || (\valid_read(t) && well_formed(t) && !trie_is_empty(t));

  predicate opt_contains{L}(TrieNode *t, unsigned char *key, integer len) =
    t != \null && trie_contains(t, key, len);

  predicate seq_eq{L}(unsigned char *a, integer la, unsigned char *b, integer lb) =
    la == lb && \forall integer i; 0 <= i < la ==> a[i] == b[i];
*/

/*@
  // Verus: fn delete(tree: Option<Box<Node>>, key: Seq<u8>) -> (res: Option<Box<Node>>)
  requires opt_well_formed(t);
  requires len >= 0;
  requires len == 0 || \valid_read(key + (0 .. len - 1));
  assigns \nothing;
  ensures opt_well_formed(\result);
  // The deleted key is no longer present.
  ensures !opt_contains(\result, (unsigned char *)key, len);
  // Frame: every other key has the same membership as before.
  ensures \forall unsigned char *k, integer kl;
    !seq_eq(k, kl, (unsigned char *)key, len) ==>
      (opt_contains(\result, k, kl) <==> opt_contains{Pre}(t, k, kl));
*/
TrieNode *trie_delete(TrieNode *t, const unsigned char *key, size_t len) {
  // Implement and verify trie_delete here.
}
