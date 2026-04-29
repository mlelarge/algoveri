#include <stddef.h>
#include <stdint.h>

// Verus: pub struct CapacityGraph { pub adj: Vec<Vec<(usize, i64)>> }
// C uses CSR (cf. dijkstra.c): col_weight[e] holds the capacity of edge e.
typedef struct {
  size_t n;
  const size_t *row_ptr;          // length n + 1
  const size_t *col_idx;          // length row_ptr[n]
  const int64_t *col_weight;      // length row_ptr[n]   (capacities)
} CapacityGraph;

/*@
  // Verus: pub open spec fn well_formed(&self) -> bool — bounds + simple-graph.
  predicate well_formed{L}(CapacityGraph *g) =
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

  // Verus: pub open spec fn has_capacity(g, u, v, c) -> bool
  predicate has_capacity{L}(CapacityGraph *g, integer u, integer v, integer c) =
    0 <= u < g->n && 0 <= v < g->n &&
    \exists integer e;
      g->row_ptr[u] <= e < g->row_ptr[u + 1] &&
      g->col_idx[e] == v &&
      g->col_weight[e] == c;

  // Verus: pub open spec fn capacities_bounded(g) -> bool
  predicate capacities_bounded{L}(CapacityGraph *g) =
    g->n <= 1000 &&
    \forall integer u, e;
      0 <= u < g->n &&
      g->row_ptr[u] <= e < g->row_ptr[u + 1] ==>
      0 <= g->col_weight[e] <= 100000;

  // Flow is represented as a row-major n x n matrix f[u * n + v] (int64_t).
  // Verus's `f.dom().contains((u,v))` is implicitly true for all (u,v) in [0,n)^2.

  // Verus: pub open spec fn get_flow(f, u, v) -> int
  // In our representation, get_flow == f[u*n + v] for in-bounds (u, v).

  // Verus: pub open spec fn respects_capacity(g, f) -> bool
  predicate respects_capacity{L}(CapacityGraph *g, int64_t *f) =
    \forall integer u, v; 0 <= u < g->n && 0 <= v < g->n &&
      f[u * (integer)g->n + v] > 0 ==>
        \exists integer c; has_capacity(g, u, v, c) && f[u * (integer)g->n + v] <= c;

  // Verus: pub open spec fn sum_flow_out_recursive(g, f, u, idx) -> int  decreases idx
  // Sum of f[u, g.adj[u][k].0] for k in [0, idx). In CSR terms: sum over the
  // first `idx` outgoing edges of u.
  axiomatic FlowSums {
    logic integer sum_flow_out_recursive{L}(CapacityGraph *g, int64_t *f,
                                              integer u, integer idx)
      reads g->n, g->row_ptr[0 .. g->n], g->col_idx[0 .. g->row_ptr[g->n] - 1],
            f[0 .. (integer)g->n * (integer)g->n - 1];

    axiom sum_flow_out_zero{L}:
      \forall CapacityGraph *g, int64_t *f, integer u, integer idx;
        idx <= 0 ==> sum_flow_out_recursive(g, f, u, idx) == 0;

    axiom sum_flow_out_step{L}:
      \forall CapacityGraph *g, int64_t *f, integer u, integer idx;
        idx > 0 ==>
          sum_flow_out_recursive(g, f, u, idx) ==
            sum_flow_out_recursive(g, f, u, idx - 1) +
            f[u * (integer)g->n + g->col_idx[g->row_ptr[u] + idx - 1]];

    // Verus: pub open spec fn sum_flow_in_recursive(g, f, u, v_idx) -> int  decreases v_idx
    // Sum of f[v, u] for v in [0, v_idx).
    logic integer sum_flow_in_recursive{L}(CapacityGraph *g, int64_t *f,
                                             integer u, integer v_idx)
      reads g->n, f[0 .. (integer)g->n * (integer)g->n - 1];

    axiom sum_flow_in_zero{L}:
      \forall CapacityGraph *g, int64_t *f, integer u, integer v_idx;
        v_idx <= 0 ==> sum_flow_in_recursive(g, f, u, v_idx) == 0;

    axiom sum_flow_in_step{L}:
      \forall CapacityGraph *g, int64_t *f, integer u, integer v_idx;
        v_idx > 0 ==>
          sum_flow_in_recursive(g, f, u, v_idx) ==
            sum_flow_in_recursive(g, f, u, v_idx - 1) +
            f[(v_idx - 1) * (integer)g->n + u];
  }

  // Verus: pub open spec fn total_flow_out(g, f, u) -> int  ::= sum over g.adj[u]
  logic integer total_flow_out{L}(CapacityGraph *g, int64_t *f, integer u) =
    sum_flow_out_recursive(g, f, u, g->row_ptr[u + 1] - g->row_ptr[u]);

  // Verus: pub open spec fn total_flow_in(g, f, u) -> int  ::= sum over all v
  logic integer total_flow_in{L}(CapacityGraph *g, int64_t *f, integer u) =
    sum_flow_in_recursive(g, f, u, g->n);

  // Verus: pub open spec fn is_conserved(g, f, s, t) -> bool
  predicate is_conserved{L}(CapacityGraph *g, int64_t *f, integer s, integer t) =
    \forall integer u; 0 <= u < g->n && u != s && u != t ==>
      total_flow_in(g, f, u) == total_flow_out(g, f, u);

  // Verus: pub open spec fn is_valid_flow(g, f, s, t) -> bool
  predicate is_valid_flow{L}(CapacityGraph *g, int64_t *f, integer s, integer t) =
    respects_capacity(g, f) &&
    is_conserved(g, f, s, t) &&
    (\forall integer u, v; 0 <= u < g->n && 0 <= v < g->n ==>
       f[u * (integer)g->n + v] >= 0);

  // Verus: pub open spec fn flow_val(g, f, s) -> int
  logic integer flow_val{L}(CapacityGraph *g, int64_t *f, integer s) =
    total_flow_out(g, f, s) - total_flow_in(g, f, s);

  // Verus: pub open spec fn is_max_flow(g, f, s, t) -> bool
  predicate is_max_flow{L}(CapacityGraph *g, int64_t *f, integer s, integer t) =
    is_valid_flow(g, f, s, t) &&
    (\forall int64_t *other;
       is_valid_flow(g, other, s, t) ==>
         flow_val(g, f, s) >= flow_val(g, other, s));
*/

/*@
  // Verus: fn max_flow_value(graph, s, t) -> (max_val: i64)
  //   ensures exists |f|. is_max_flow(g, f, s, t) && flow_val(g, f, s) == max_val
  // C: caller passes a flow buffer (n*n int64_t) which the function fills.
  requires well_formed(g);
  requires capacities_bounded(g);
  requires 0 <= s < g->n;
  requires 0 <= t < g->n;
  requires s != t;
  requires \valid(f + (0 .. (integer)g->n * (integer)g->n - 1));
  assigns f[0 .. (integer)g->n * (integer)g->n - 1];
  ensures is_max_flow(g, f, s, t);
  ensures \result == flow_val(g, f, s);
*/
int64_t max_flow_value(const CapacityGraph *g, size_t s, size_t t, int64_t *f) {
  // Implement and verify max_flow_value (Edmonds-Karp) here.
}
