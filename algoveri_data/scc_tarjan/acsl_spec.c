#include <stddef.h>

// Verus: pub struct Graph { pub adj: Vec<Vec<usize>> }
// C uses CSR (see topological_sort.c).
typedef struct {
  size_t n;
  const size_t *row_ptr;
  const size_t *col_idx;
} Graph;

/*@
  // Verus: pub open spec fn well_formed(&self) -> bool
  predicate well_formed{L}(Graph *g) =
    \valid_read(g) &&
    \valid_read(g->row_ptr + (0 .. g->n)) &&
    g->row_ptr[0] == 0 &&
    (\forall integer v; 0 <= v < g->n ==> g->row_ptr[v] <= g->row_ptr[v + 1]) &&
    (g->row_ptr[g->n] == 0 || \valid_read(g->col_idx + (0 .. g->row_ptr[g->n] - 1))) &&
    (\forall integer v; 0 <= v < g->n ==>
      \forall integer e; g->row_ptr[v] <= e < g->row_ptr[v + 1] ==>
        g->col_idx[e] < g->n);

  // Verus: g.size() <= 1000
  predicate size_bounded{L}(Graph *g) = g->n <= 1000;

  predicate has_edge{L}(Graph *g, integer u, integer v) =
    0 <= u < g->n && 0 <= v < g->n &&
    \exists integer e; g->row_ptr[u] <= e < g->row_ptr[u + 1] && g->col_idx[e] == v;

  // path_valid: every consecutive pair in p is connected by an edge.
  predicate path_valid{L}(Graph *g, int *p, integer plen) =
    \forall integer k; 0 <= k < plen - 1 ==>
      has_edge(g, p[k], p[k + 1]);

  // Reachability: there exists a path from u to v.
  predicate has_path{L}(Graph *g, integer u, integer v) =
    \exists int *p, integer plen;
      plen > 0 && \valid_read(p + (0 .. plen - 1)) &&
      p[0] == u && p[plen - 1] == v && path_valid(g, p, plen);

  // Components are encoded as comp[v] = id, with 0 <= id < k.
  // Two vertices share an SCC iff they share a comp id.

  // Verus: pub open spec fn is_strongly_connected
  predicate is_strongly_connected{L}(Graph *g, int *comp) =
    \forall integer u, v; 0 <= u < g->n && 0 <= v < g->n && comp[u] == comp[v] ==>
      has_path(g, u, v) && has_path(g, v, u);

  // Verus: pub open spec fn is_maximal_scc_structure
  predicate is_maximal_scc{L}(Graph *g, int *comp) =
    \forall integer u, v; 0 <= u < g->n && 0 <= v < g->n && comp[u] != comp[v] ==>
      !(has_path(g, u, v) && has_path(g, v, u));

  // Verus: pub open spec fn is_valid_scc_result
  predicate is_valid_scc_result{L}(Graph *g, int *comp, integer k) =
    (\forall integer v; 0 <= v < g->n ==> 0 <= comp[v] < k) &&
    is_strongly_connected(g, comp) &&
    is_maximal_scc(g, comp);
*/

/*@
  // Verus: fn find_sccs(graph: &Graph) -> (sccs: Vec<Vec<usize>>)
  // C: writes comp[v] = component id; returns the number of components.
  requires well_formed(g);
  requires size_bounded(g);
  requires \valid(comp + (0 .. g->n - 1));
  assigns comp[0 .. g->n - 1];
  ensures 0 <= \result <= g->n;
  ensures is_valid_scc_result(g, comp, \result);
*/
int find_sccs(const Graph *g, int *comp) {
  // Implement and verify find_sccs here.
}
