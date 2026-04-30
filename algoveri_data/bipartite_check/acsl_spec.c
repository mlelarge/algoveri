#include <stddef.h>
#include <stdint.h>

// Verus: pub struct Graph { pub adj: Vec<Vec<usize>> }
// C uses CSR (cf. topological_sort.c).
typedef struct {
  size_t n;
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

  // Verus: pub open spec fn is_valid_coloring(g, colors) -> bool
  // Colors are encoded as {0, 1} (false / true). Caller passes an array of size g->n.
  predicate is_valid_coloring{L}(Graph *g, int *colors) =
    \valid_read(colors + (0 .. g->n - 1)) &&
    (\forall integer v; 0 <= v < g->n ==> (colors[v] == 0 || colors[v] == 1)) &&
    (\forall integer u, v; 0 <= u < g->n && 0 <= v < g->n && has_edge(g, u, v) ==>
       colors[u] != colors[v]);

  // Verus: pub open spec fn is_bipartite(g) -> bool
  predicate is_bipartite{L}(Graph *g) =
    \exists int *colors; is_valid_coloring(g, colors);
*/

/*@
  // Verus: fn check_bipartite(graph: &Graph) -> (res: Option<Vec<bool>>)
  //   ensures match res {
  //     Some(colors) => is_valid_coloring(g, colors),
  //     None => !is_bipartite(g) }
  // C: returns 1 and writes colors[] on success, returns 0 on failure.
  requires well_formed(g);
  requires \valid(colors + (0 .. g->n - 1));
  requires \separated(colors + (0 .. g->n - 1), g);
  requires \separated(colors + (0 .. g->n - 1), g->row_ptr + (0 .. g->n));
  requires g->row_ptr[g->n] == 0 ||
           \separated(colors + (0 .. g->n - 1),
                      g->col_idx + (0 .. g->row_ptr[g->n] - 1));
  assigns colors[0 .. g->n - 1];
  ensures \result == 0 || \result == 1;
  ensures \result == 1 ==> is_valid_coloring(g, colors);
  ensures \result == 0 ==> !is_bipartite(g);
*/
int check_bipartite(const Graph *g, int *colors) {
  // Implement and verify check_bipartite here.
}
