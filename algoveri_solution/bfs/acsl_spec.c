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

  // Verus: g.size() <= 10000
  predicate size_bounded{L}(Graph *g) = g->n <= 10000;

  // Verus: pub open spec fn has_edge(g, u, v) -> bool
  predicate has_edge{L}(Graph *g, integer u, integer v) =
    0 <= u < g->n && 0 <= v < g->n &&
    \exists integer e; g->row_ptr[u] <= e < g->row_ptr[u + 1] && g->col_idx[e] == v;

  // Verus: pub open spec fn is_path(g, p) -> bool
  predicate is_path{L}(Graph *g, int *p, integer plen) =
    plen > 0 &&
    \valid_read(p + (0 .. plen - 1)) &&
    \forall integer k; 0 <= k < plen - 1 ==>
      has_edge(g, p[k], p[k + 1]);

  // Verus: pub open spec fn reachable(g, start, end) -> bool
  predicate reachable{L}(Graph *g, integer start, integer end) =
    \exists int *p, integer plen;
      is_path(g, p, plen) &&
      p[0] == start && p[plen - 1] == end;

  // Verus: pub open spec fn is_shortest_distance(g, start, end, d) -> bool
  // Note: distance is measured in *edges* (path length d <==> p.len() == d + 1).
  predicate is_shortest_distance{L}(Graph *g, integer start, integer end, integer d) =
    (\exists int *p, integer plen;
       is_path(g, p, plen) &&
       p[0] == start && p[plen - 1] == end &&
       plen == d + 1) &&
    (\forall int *p, integer plen;
       is_path(g, p, plen) &&
       p[0] == start && p[plen - 1] == end ==>
       plen >= d + 1);
*/

/*@
  // Verus: fn bfs_shortest_path(graph, start, target) -> (res: Option<u64>)
  //   ensures match res {
  //     Some(d) => is_shortest_distance(start, target, d),
  //     None => !reachable(start, target) }
  // C: \result >= 0 is the distance; \result == -1 means unreachable.
  requires well_formed(g);
  requires size_bounded(g);
  requires 0 <= start < g->n;
  requires 0 <= target < g->n;
  assigns \nothing;
  ensures \result >= -1;
  ensures \result == -1 <==> !reachable(g, start, target);
  ensures \result >= 0 ==>
    is_shortest_distance(g, start, target, \result);
*/
int bfs_shortest_path(const Graph *g, size_t start, size_t target) {
  // Implement and verify bfs_shortest_path here.
}
