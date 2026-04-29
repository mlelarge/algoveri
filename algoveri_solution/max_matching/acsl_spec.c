#include <stddef.h>
#include <stdint.h>

// Verus: pub struct BipartiteGraph { left_size, right_size, adj: Vec<Vec<usize>> }
// adj has length left_size; entries are right-side indices in [0, right_size).
// C uses CSR over the left side: row_ptr[0..left_size], col_idx[..] in [0, right_size).
typedef struct {
  size_t left_size;
  size_t right_size;
  const size_t *row_ptr;   // length left_size + 1
  const size_t *col_idx;   // length row_ptr[left_size]
} BipartiteGraph;

/*@
  // Verus: pub open spec fn well_formed(&self) -> bool
  predicate well_formed{L}(BipartiteGraph *g) =
    \valid_read(g) &&
    \valid_read(g->row_ptr + (0 .. g->left_size)) &&
    g->row_ptr[0] == 0 &&
    (\forall integer u; 0 <= u < g->left_size ==> g->row_ptr[u] <= g->row_ptr[u + 1]) &&
    (g->row_ptr[g->left_size] == 0 ||
       \valid_read(g->col_idx + (0 .. g->row_ptr[g->left_size] - 1))) &&
    (\forall integer u; 0 <= u < g->left_size ==>
      \forall integer e; g->row_ptr[u] <= e < g->row_ptr[u + 1] ==>
        g->col_idx[e] < g->right_size);

  // Verus: pub open spec fn size_bounded(g) -> bool
  predicate size_bounded{L}(BipartiteGraph *g) =
    g->left_size <= 1000 && g->right_size <= 1000;

  // A matching is a Set<(int, int)> in Verus. We encode it as parallel arrays
  // mu[k], mv[k] for k in [0, mlen): mu[k] is the left endpoint, mv[k] the right.

  // Verus: pub open spec fn matching_valid_edges(g, m) -> bool
  // Each edge (mu[k], mv[k]) must come from g's adjacency list.
  predicate matching_valid_edges{L}(BipartiteGraph *g, int *mu, int *mv, integer mlen) =
    \valid_read(mu + (0 .. mlen - 1)) &&
    \valid_read(mv + (0 .. mlen - 1)) &&
    (\forall integer k; 0 <= k < mlen ==>
       0 <= mu[k] < g->left_size &&
       (\exists integer e;
          g->row_ptr[mu[k]] <= e < g->row_ptr[mu[k] + 1] &&
          g->col_idx[e] == mv[k]));

  // Verus: pub open spec fn is_disjoint(m) -> bool
  // No two distinct edges share a left or right endpoint.
  predicate is_disjoint{L}(int *mu, int *mv, integer mlen) =
    \forall integer i, j; 0 <= i < mlen && 0 <= j < mlen && i != j ==>
      mu[i] != mu[j] && mv[i] != mv[j];

  // Verus: pub open spec fn is_matching(g, m) -> bool
  predicate is_matching{L}(BipartiteGraph *g, int *mu, int *mv, integer mlen) =
    matching_valid_edges(g, mu, mv, mlen) &&
    is_disjoint(mu, mv, mlen);

  // Verus: pub open spec fn is_max_matching(g, m) -> bool
  // Note: Verus uses Set semantics (m.len() = number of distinct edges). With
  // is_disjoint, our parallel-array encoding has no duplicates, so |m| == mlen.
  predicate is_max_matching{L}(BipartiteGraph *g, int *mu, int *mv, integer mlen) =
    is_matching(g, mu, mv, mlen) &&
    (\forall int *ou, int *ov, integer olen;
       is_matching(g, ou, ov, olen) ==> mlen >= olen);
*/

/*@
  // Verus: fn max_bipartite_matching(graph) -> (size: usize)
  //   ensures exists |m|. is_max_matching(g, m) && m.len() == size
  // C: returns the size; the witness matching is not exposed (existential is enough).
  requires well_formed(g);
  requires size_bounded(g);
  assigns \nothing;
  ensures 0 <= \result;
  ensures \result <= g->left_size;
  ensures \result <= g->right_size;
  ensures \exists int *mu, int *mv;
            is_max_matching(g, mu, mv, \result);
*/
size_t max_bipartite_matching(const BipartiteGraph *g) {
  // Implement and verify max_bipartite_matching here.
}
