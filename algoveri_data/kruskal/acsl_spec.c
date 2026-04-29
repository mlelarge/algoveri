#include <stddef.h>
#include <stdint.h>

// Verus: pub struct WeightedGraph { pub adj: Vec<Vec<(usize, i64)>> }
// C uses CSR (cf. dijkstra.c). Identical preamble to prim.rs.
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

  // Verus: pub open spec fn weights_bounded(g) -> bool
  predicate weights_bounded{L}(WeightedGraph *g) =
    g->n <= 100000 &&
    \forall integer u, e;
      0 <= u < g->n &&
      g->row_ptr[u] <= e < g->row_ptr[u + 1] ==>
      -100000 <= g->col_weight[e] <= 100000;

  // Verus: pub open spec fn are_valid_edges(g, edges) -> bool
  predicate are_valid_edges{L}(WeightedGraph *g, int *eu, int *ev, int64_t *ew, integer elen) =
    \valid_read(eu + (0 .. elen - 1)) &&
    \valid_read(ev + (0 .. elen - 1)) &&
    \valid_read(ew + (0 .. elen - 1)) &&
    (\forall integer k; 0 <= k < elen ==> has_edge(g, eu[k], ev[k], ew[k]));

  // Verus: pub open spec fn edge_in_set(edges, u, v) -> bool  (undirected)
  predicate edge_in_set{L}(int *eu, int *ev, integer elen, integer u, integer v) =
    \exists integer k;
      0 <= k < elen &&
      ((eu[k] == u && ev[k] == v) || (eu[k] == v && ev[k] == u));

  // Verus: pub open spec fn path_follows_edges(edges, p) -> bool
  predicate path_follows_edges{L}(int *eu, int *ev, integer elen, int *p, integer plen) =
    \forall integer k; 0 <= k < plen - 1 ==>
      edge_in_set(eu, ev, elen, p[k], p[k + 1]);

  // Verus: pub open spec fn edges_connected(edges, u, v) -> bool
  predicate edges_connected{L}(int *eu, int *ev, integer elen, integer u, integer v) =
    \exists int *p, integer plen;
      plen > 0 && \valid_read(p + (0 .. plen - 1)) &&
      p[0] == u && p[plen - 1] == v &&
      path_follows_edges(eu, ev, elen, p, plen);

  // Verus: pub open spec fn is_spanning(g, edges) -> bool
  predicate is_spanning{L}(WeightedGraph *g, int *eu, int *ev, integer elen) =
    \forall integer u, v; 0 <= u < g->n && 0 <= v < g->n ==>
      edges_connected(eu, ev, elen, u, v);

  // Verus: pub open spec fn is_spanning_tree(g, edges) -> bool
  predicate is_spanning_tree{L}(WeightedGraph *g, int *eu, int *ev, int64_t *ew, integer elen) =
    are_valid_edges(g, eu, ev, ew, elen) &&
    is_spanning(g, eu, ev, elen) &&
    elen == g->n - 1;

  // Verus: pub open spec fn total_weight(edges) -> int  decreases edges.len()
  axiomatic KruskalTotalWeight {
    logic integer total_weight{L}(int64_t *ew, integer elen)
      reads ew[0 .. elen - 1];

    axiom total_weight_zero{L}:
      \forall int64_t *ew, integer elen;
        elen <= 0 ==> total_weight(ew, elen) == 0;

    axiom total_weight_step{L}:
      \forall int64_t *ew, integer elen;
        elen > 0 ==>
          total_weight(ew, elen) == total_weight(ew, elen - 1) + ew[elen - 1];
  }

  // Verus: pub open spec fn is_mst(g, edges) -> bool
  predicate is_mst{L}(WeightedGraph *g, int *eu, int *ev, int64_t *ew, integer elen) =
    is_spanning_tree(g, eu, ev, ew, elen) &&
    (\forall int *ou, int *ov, int64_t *ow, integer olen;
       is_spanning_tree(g, ou, ov, ow, olen) ==>
         total_weight(ew, elen) <= total_weight(ow, olen));

  // Verus: pub open spec fn graph_has_any_edge(g, u, v) -> bool
  predicate graph_has_any_edge{L}(WeightedGraph *g, integer u, integer v) =
    0 <= u < g->n && 0 <= v < g->n &&
    \exists integer e; g->row_ptr[u] <= e < g->row_ptr[u + 1] && g->col_idx[e] == v;

  predicate path_follows_graph{L}(WeightedGraph *g, int *p, integer plen) =
    \forall integer k; 0 <= k < plen - 1 ==>
      graph_has_any_edge(g, p[k], p[k + 1]);

  predicate nodes_have_path{L}(WeightedGraph *g, integer u, integer v) =
    \exists int *p, integer plen;
      plen > 0 && \valid_read(p + (0 .. plen - 1)) &&
      p[0] == u && p[plen - 1] == v &&
      path_follows_graph(g, p, plen);

  predicate graph_is_connected{L}(WeightedGraph *g) =
    \forall integer u, v; 0 <= u < g->n && 0 <= v < g->n ==>
      nodes_have_path(g, u, v);
*/

/*@
  // Verus: fn kruskal_mst(graph: &WeightedGraph) -> (edges: Vec<(usize, usize, i64)>)
  //   ensures is_mst(graph.view(), edges@.map_values(...))
  // C: caller passes output arrays (out_u, out_v, out_w) of capacity g->n - 1;
  //    function returns the number of edges (== g->n - 1 on success).
  requires well_formed(g);
  requires g->n > 0;
  requires weights_bounded(g);
  requires graph_is_connected(g);
  requires \valid(out_u + (0 .. g->n - 1));
  requires \valid(out_v + (0 .. g->n - 1));
  requires \valid(out_w + (0 .. g->n - 1));
  assigns out_u[0 .. g->n - 1], out_v[0 .. g->n - 1], out_w[0 .. g->n - 1];
  ensures \result == g->n - 1;
  ensures is_mst(g, out_u, out_v, out_w, \result);
*/
size_t kruskal_mst(const WeightedGraph *g, int *out_u, int *out_v, int64_t *out_w) {
  // Implement and verify kruskal_mst here.
}
