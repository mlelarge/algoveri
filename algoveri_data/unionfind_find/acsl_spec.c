#include <stddef.h>

// Verus: pub struct UnionFind { pub parent: Vec<usize>, pub rank: Vec<usize> }
typedef struct {
  size_t *parent;
  size_t *rank;
  size_t n;          // shared length
} UnionFind;

/*@
  // Verus: pub open spec fn is_valid(&self) -> bool
  predicate is_valid_uf{L}(UnionFind *uf) =
    \valid(uf) &&
    (uf->n == 0 ||
      (\valid(uf->parent + (0 .. uf->n - 1)) &&
       \valid(uf->rank + (0 .. uf->n - 1)))) &&
    \forall integer i; 0 <= i < uf->n ==>
      uf->parent[i] < uf->n &&
      uf->rank[i] < uf->n &&
      (uf->parent[i] != i ==> uf->rank[i] < uf->rank[uf->parent[i]]);

  axiomatic UnionFindFind {
    // Verus: pub open spec fn spec_find(&self, i: usize) -> usize  decreases self.measure(i)
    // Defining recursion: follow parent links while the rank-strict-increase
    // condition holds, otherwise return i.
    logic integer spec_find{L}(UnionFind *uf, integer i)
      reads uf, uf->parent, uf->rank, uf->n,
            uf->parent[0 .. uf->n - 1], uf->rank[0 .. uf->n - 1];

    axiom spec_find_root{L}:
      \forall UnionFind *uf, integer i;
        0 <= i < uf->n && uf->parent[i] == i ==>
          spec_find(uf, i) == i;

    axiom spec_find_step{L}:
      \forall UnionFind *uf, integer i;
        0 <= i < uf->n && uf->parent[i] != i &&
        0 <= uf->parent[i] < uf->n &&
        uf->rank[i] < uf->rank[uf->parent[i]] ==>
          spec_find(uf, i) == spec_find(uf, uf->parent[i]);
  }
*/

/*@
  // Verus: pub fn find(&mut self, i: usize) -> (root: usize)
  requires is_valid_uf(uf);
  requires 0 <= i < uf->n;
  assigns uf->parent[0 .. uf->n - 1];
  ensures is_valid_uf(uf);
  ensures \result == spec_find{Pre}(uf, i);
  // The representative of every element is preserved under path compression.
  ensures \forall integer j; 0 <= j < uf->n ==>
    spec_find(uf, j) == spec_find{Pre}(uf, j);
  // Frame: rank and length are unchanged.
  ensures \forall integer k; 0 <= k < uf->n ==>
    uf->rank[k] == \at(uf->rank[k], Pre);
  ensures uf->n == \at(uf->n, Pre);
*/
size_t uf_find(UnionFind *uf, size_t i) {
  // Implement and verify uf_find here.
}
