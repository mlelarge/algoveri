#include <stddef.h>
#include <stdint.h>

// Verus: pub struct WeightedGraph { pub adj: Vec<Vec<(usize, i64)>> }
// C uses CSR (cf. topological_sort.c) extended with a parallel weight array:
//   row_ptr[v]    : start index in (col_idx, col_weight) for v's neighbours
//   col_idx[e]    : neighbour vertex
//   col_weight[e] : edge weight to that neighbour
typedef struct {
  size_t n;
  const size_t *row_ptr;          // length n + 1
  const size_t *col_idx;          // length row_ptr[n]
  const int64_t *col_weight;      // length row_ptr[n]
} WeightedGraph;

/*@
  // Verus: pub open spec fn well_formed(&self) -> bool — bounds + simple-graph.
  predicate well_formed{L}(WeightedGraph *g) =
    \valid_read(g) &&
    \valid_read(g->row_ptr + (0 .. g->n)) &&
    g->row_ptr[0] == 0 &&
    (\forall integer v; 0 <= v < g->n ==> g->row_ptr[v] <= g->row_ptr[v + 1]) &&
    (g->row_ptr[g->n] == 0 ||
       (\valid_read(g->col_idx + (0 .. g->row_ptr[g->n] - 1)) &&
        \valid_read(g->col_weight + (0 .. g->row_ptr[g->n] - 1)))) &&
    (\forall integer v; 0 <= v < g->n ==>
      \forall integer e; g->row_ptr[v] <= e < g->row_ptr[v + 1] ==>
        g->col_idx[e] < g->n) &&
    // Simple-graph constraint: no duplicate edges from u to the same v.
    (\forall integer u, e1, e2;
      0 <= u < g->n &&
      g->row_ptr[u] <= e1 < g->row_ptr[u + 1] &&
      g->row_ptr[u] <= e2 < g->row_ptr[u + 1] &&
      e1 != e2 ==> g->col_idx[e1] != g->col_idx[e2]);

  // Verus: pub open spec fn has_edge(g, u, v, w) -> bool
  predicate has_edge{L}(WeightedGraph *g, integer u, integer v, integer weight) =
    0 <= u < g->n && 0 <= v < g->n &&
    \exists integer e;
      g->row_ptr[u] <= e < g->row_ptr[u + 1] &&
      g->col_idx[e] == v &&
      g->col_weight[e] == weight;

  // Verus: pub open spec fn connected(g, u, v) -> bool
  predicate connected{L}(WeightedGraph *g, integer u, integer v) =
    \exists integer weight; has_edge(g, u, v, weight);

  // Verus: pub open spec fn is_path(g, p) -> bool
  predicate is_path{L}(WeightedGraph *g, int *p, integer plen) =
    plen > 0 &&
    \valid_read(p + (0 .. plen - 1)) &&
    \forall integer k; 0 <= k < plen - 1 ==> connected(g, p[k], p[k + 1]);

  // Verus: pub open spec fn weights_non_negative(g) -> bool
  predicate weights_non_negative{L}(WeightedGraph *g) =
    \forall integer u, e;
      0 <= u < g->n &&
      g->row_ptr[u] <= e < g->row_ptr[u + 1] ==>
      g->col_weight[e] >= 0;

  // Verus: pub open spec fn weights_and_size_bounded(g) -> bool
  predicate weights_and_size_bounded{L}(WeightedGraph *g) =
    g->n <= 100000 &&
    \forall integer u, e;
      0 <= u < g->n &&
      g->row_ptr[u] <= e < g->row_ptr[u + 1] ==>
      -100000 <= g->col_weight[e] <= 100000;

  // Verus: pub open spec fn path_weight(g, p) -> int  decreases p.len()
  // Under well_formed's simple-graph constraint, edge_weight(u, v) is uniquely
  // defined for connected pairs.
  axiomatic DijkstraPathWeight {
    logic integer edge_weight{L}(WeightedGraph *g, integer u, integer v)
      reads g->n, g->row_ptr[0 .. g->n], g->col_idx[0 .. g->row_ptr[g->n] - 1],
            g->col_weight[0 .. g->row_ptr[g->n] - 1];

    axiom edge_weight_pick{L}:
      \forall WeightedGraph *g, integer u, integer v, integer weight;
        well_formed(g) && has_edge(g, u, v, weight) ==>
        edge_weight(g, u, v) == weight;

    logic integer path_weight{L}(WeightedGraph *g, int *p, integer plen)
      reads g->n, g->row_ptr[0 .. g->n], g->col_idx[0 .. g->row_ptr[g->n] - 1],
            g->col_weight[0 .. g->row_ptr[g->n] - 1], p[0 .. plen - 1];

    axiom path_weight_short{L}:
      \forall WeightedGraph *g, int *p, integer plen;
        plen < 2 ==> path_weight(g, p, plen) == 0;

    axiom path_weight_step{L}:
      \forall WeightedGraph *g, int *p, integer plen;
        plen >= 2 ==>
          path_weight(g, p, plen) ==
            path_weight(g, p, plen - 1) +
            edge_weight(g, p[plen - 2], p[plen - 1]);
  }

  // Verus: pub open spec fn is_shortest_dist(g, start, end, d) -> bool
  predicate is_shortest_dist{L}(WeightedGraph *g, integer start, integer end, integer d) =
    (\exists int *p, integer plen;
       is_path(g, p, plen) &&
       p[0] == start && p[plen - 1] == end &&
       path_weight(g, p, plen) == d) &&
    (\forall int *p, integer plen;
       is_path(g, p, plen) && p[0] == start && p[plen - 1] == end ==>
       path_weight(g, p, plen) >= d);

  // No path from start ever lands on v.
  predicate unreachable_from{L}(WeightedGraph *g, integer start, integer v) =
    \forall int *p, integer plen;
      is_path(g, p, plen) && p[0] == start ==> p[plen - 1] != v;
*/

/*@
  // Verus: fn dijkstra_shortest_paths(graph: &WeightedGraph, start: usize)
  //          -> (res: Vec<Option<i64>>)
  //   ensures res.len() == graph.size()
  //        /\ forall v. match res[v] { Some(d) => is_shortest_dist(start, v, d),
  //                                     None    => unreachable_from(start, v) }
  // C: dist[v] holds the distance, reachable[v] is the Some/None discriminator.
  requires well_formed(g);
  requires weights_non_negative(g);
  requires weights_and_size_bounded(g);
  requires 0 <= start < g->n;
  requires \valid(dist + (0 .. g->n - 1));
  requires \valid(reachable + (0 .. g->n - 1));
  assigns dist[0 .. g->n - 1], reachable[0 .. g->n - 1];
  ensures \forall integer v; 0 <= v < g->n ==>
            (reachable[v] == 0 || reachable[v] == 1);
  ensures \forall integer v; 0 <= v < g->n && reachable[v] == 1 ==>
            is_shortest_dist(g, start, v, dist[v]);
  ensures \forall integer v; 0 <= v < g->n && reachable[v] == 0 ==>
            unreachable_from(g, start, v);
*/
void dijkstra_shortest_paths(const WeightedGraph *g, size_t start,
                             int64_t *dist, int *reachable) {
  // Implement and verify dijkstra_shortest_paths here.
}
