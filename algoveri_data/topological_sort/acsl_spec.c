#include <stddef.h>
#include <stdint.h>

// Verus: pub struct Graph { pub adj: Vec<Vec<usize>> }
// C uses CSR: row_ptr[v] gives the start index in col_idx of v's neighbours;
// row_ptr[v+1] - row_ptr[v] is the out-degree of v.
typedef struct {
  size_t n;                // number of vertices
  const size_t *row_ptr;   // length n + 1
  const size_t *col_idx;   // length row_ptr[n]
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

  // Verus: pub open spec fn has_edge(g, u, v) -> bool
  predicate has_edge{L}(Graph *g, integer u, integer v) =
    0 <= u < g->n && 0 <= v < g->n &&
    \exists integer e; g->row_ptr[u] <= e < g->row_ptr[u + 1] && g->col_idx[e] == v;

  // Verus: pub open spec fn is_path(g, p: Seq<int>) -> bool
  predicate is_path{L}(Graph *g, int *p, integer plen) =
    plen > 0 &&
    \forall integer k; 0 <= k < plen - 1 ==>
      has_edge(g, p[k], p[k + 1]);

  // Verus: pub open spec fn is_cycle(g, p) -> bool
  predicate is_cycle{L}(Graph *g, int *p, integer plen) =
    is_path(g, p, plen) && plen > 1 && p[0] == p[plen - 1];

  // Verus: pub open spec fn graph_has_cycle(g) -> bool
  predicate graph_has_cycle{L}(Graph *g) =
    \exists int *p, integer plen;
      plen > 0 && \valid_read(p + (0 .. plen - 1)) && is_cycle(g, p, plen);

  // Verus: pub open spec fn is_topological_ordering(g, order: Seq<int>) -> bool
  predicate is_topological_ordering{L}(Graph *g, size_t *order) =
    (\forall integer i; 0 <= i < g->n ==> 0 <= order[i] < g->n) &&
    (\forall integer i, j; 0 <= i < j < g->n ==> order[i] != order[j]) &&
    (\forall integer i, j; 0 <= j < i < g->n ==>
       !has_edge(g, order[i], order[j]));
*/

/*@
  // Verus: fn topological_sort(graph: &Graph) -> (res: Option<Vec<usize>>)
  // C: returns 1 on success and writes order; returns 0 if a cycle exists.
  requires well_formed(g);
  requires \valid(order + (0 .. g->n - 1));
  assigns order[0 .. g->n - 1];
  ensures \result == 0 || \result == 1;
  ensures \result == 1 ==>
    !graph_has_cycle(g) && is_topological_ordering(g, order);
  ensures \result == 0 ==> graph_has_cycle(g);
*/
int topological_sort(const Graph *g, size_t *order) {
  // Implement and verify topological_sort here.
}
