#include <stddef.h>

typedef struct {
  size_t *parent;
  size_t *rank;
  size_t n;
} UnionFind;

/*@
  predicate is_valid_uf{L}(UnionFind *uf) =
    \valid(uf) &&
    (uf->n == 0 ||
      (\valid(uf->parent + (0 .. uf->n - 1)) &&
       \valid(uf->rank + (0 .. uf->n - 1)))) &&
    \forall integer i; 0 <= i < uf->n ==>
      uf->parent[i] < uf->n &&
      uf->rank[i] < uf->n &&
      (uf->parent[i] != i ==> uf->rank[i] < uf->rank[uf->parent[i]]);

  axiomatic UnionFindLink {
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
  // Verus: pub fn link_roots(&mut self, root_i: usize, root_j: usize)
  requires is_valid_uf(uf);
  requires 0 <= root_i < uf->n;
  requires 0 <= root_j < uf->n;
  // Both arguments must currently be roots.
  requires uf->parent[root_i] == root_i;
  requires uf->parent[root_j] == root_j;
  assigns uf->parent[0 .. uf->n - 1], uf->rank[0 .. uf->n - 1];
  ensures is_valid_uf(uf);
  ensures uf->n == \at(uf->n, Pre);
  // Functional correctness: the two roots now have the same representative.
  ensures spec_find(uf, root_i) == spec_find(uf, root_j);
  // Frame: any other vertex that was a root is still a root.
  ensures \forall integer k; 0 <= k < uf->n && k != root_i && k != root_j ==>
    (\at(uf->parent[k], Pre) == k ==> uf->parent[k] == k);
*/
void uf_link_roots(UnionFind *uf, size_t root_i, size_t root_j) {
  // Implement and verify uf_link_roots here.
}
