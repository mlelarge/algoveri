# ACSL spec realignment — provenance notes

This document records how each `algoveri_data/<name>/acsl_spec.c` in this fork
was derived from the corresponding `verus_spec.rs`. Source repository for the
ACSL work: [zak-al/acsl-benchmarks](https://github.com/zak-al/acsl-benchmarks),
branch `verus-realignment` (commit `0be94e4`). Section 1 below explains the
realignment approach; section 2 is the per-file triage that planned it;
section 3 reports the soundness probe results.

## 1. Realignment approach

The 60 problems with both a Dafny and Verus original (in
`algoveri_data/<name>/`) had been previously hand-ported to ACSL with full
implementations. To use those ports as **specs** for the AlgoVeri evaluation
(empty body, model fills in `// Implement and verify <name> here.`), the
implementations were stripped and the contracts realigned with the Verus
originals across five phases:

- **Phase 0 — inventory.** Copy each `verus_spec.rs` and produce a per-file
  delta (signature / preamble / representation) classifying every file by
  phase. The result is the table in section 2.
- **Phase 1 — cosmetic** (~24 files): `int → int32_t/size_t`, function names
  matched against Verus, `bool` returns honored, proof scaffolding dropped
  from the preamble (e.g. `sorted_suffix`, `prefix_le_suffix`,
  `swapped_adjacent` / `SwapMultiset` axiomatic, `pow2_int`,
  `pattern_matches_at`).
- **Phase 2 — predicate alignment** (~30 files): Verus `spec fn` definitions
  that the ACSL had left as bare uninterpreted `logic` declarations were
  replaced with concrete recursive `predicate` definitions or with
  `axiomatic` blocks giving the structural recursion (base + step). Affected:
  `dijkstra`, `bellman_ford`, `bfs`, `dfs`, `cycle_detection`,
  `bipartite_check`, `prim`, `kruskal`, `edmond_karp`, `push_relabel`,
  `max_matching`, `coin_change`, `knapsack_*`, `house_robber`,
  `fast_exponential`, `integer_exponential`, `discrete_logarithm`,
  `trial_division_*`, `maxheap_*`, `bracket_matching`, `ac_automata`,
  `polymul_*`, `lcs`, `lis`, `matrix_multiplication`, `linearsys_gf2`, all
  `bst_*`, all `llrbt_*`, `lca`, `jump_game`, `longest_palindrome_substring`.
- **Phase 3 — representation** (~14 files): graph algorithms switched from
  COO `(src[], dst[], w[], n, m)` to CSR `Graph { n, row_ptr, col_idx }` /
  `WeightedGraph { ..., col_weight }` to match Verus's `Vec<Vec<usize>>` /
  `Vec<Vec<(usize, i64)>>`.
- **Phase 4 — recursive datatypes** (12 files): `bst_*`, `llrbt_*`, `lca`
  aligned via shared `BstNode` / `LlrbtNode` typedefs, recursive `is_bst` /
  `is_llrbt` / `in_view` predicates, and `axiomatic` blocks for
  value-returning recursion (`view_at`, `black_height`).

The 17 problems without a `dafny_spec.dfy` or `verus_spec.rs`-only
counterpart in the legacy ACSL ports — `binary_search`, `rod_cutting`,
`scc_tarjan`, `segmenttree_*`, `sieve_method`, `splaytree_splay`,
`ternarysearchtree_*`, `topological_sort`, `trie_*`, `unionfind_*` — were
translated directly from Verus when first authored, so they did not require
realignment.

All 77 files parse cleanly with `frama-c` (front-end only).

## 2. Per-file triage

Phase distribution (overlaps possible — a file can be both Phase 2 and
Phase 3):

| Phase | Count | Goal |
|-------|-------|------|
| Phase 1 (cosmetic only) | 24 | Fix type/name mismatches |
| Phase 2 (predicate alignment) | 30 | Add recursive spec fn bodies |
| Phase 3 (representation change) | 14 | Adapt adjacency list ↔ COO |
| Phase 4 (recursive datatype) | 12 | Adapt tree structs to arrays |

Per-file table (the 60 files with a prior ACSL port — the 17 newly translated
files are not listed here):

| File | Verus fn | ACSL fn (legacy) | Recursive spec fn uninterpreted? | Repr diff | Scaffold | Phase |
|------|----------|------------------|----------------------------------|-----------|----------|-------|
| ac_automata | `ac_automata_search() -> resu...` | `int ac_automata_search` | No | Vec<Vec> | — | **3** |
| bellman_ford | `bellman_ford() -> res: Optio...` | `int bellman_ford` | Yes | Vec<Vec> (adj list) vs COO | Yes | **2, 3** |
| bfs | `bfs_shortest_path() -> res: ...` | `int bfs_shortest_path` | No | Vec<Vec> (adj list) vs COO | Yes | **3** |
| bipartite_check | `main()` | `int check_bipartite` | No | Vec<Vec> (adj list) vs COO | Yes | **3** |
| bracket_matching | `bracket_match() -> res: bool` | `int bracket_match` | Yes | — | — | **2** |
| bst_delete | `main()` | `int delete_bst_set` | Yes | Box<Node> tree vs array | — | **2, 4** |
| bst_insert | `main()` | `int insert_bst_set` | Yes | Box<Node> tree vs array | — | **2, 4** |
| bst_search | `main()` | `int search_bst_set` | Yes | Box<Node> tree vs array | — | **2, 4** |
| bst_zig | `main()` | `void zig_rotate` | Yes | Box<Node> tree vs array | — | **2, 4** |
| bst_zigzag | `main()` | `void zig_zag_rotate` | Yes | Box<Node> tree vs array | — | **2, 4** |
| bst_zigzig | `main()` | `void zig_zig_rotate` | Yes | Box<Node> tree vs array | — | **2, 4** |
| bubble_sort | `bubble_sort()` | `void bubble_sort` | No | — | Yes | **1** |
| coin_change | `coin_change() -> min_coins: ...` | `int coin_change` | Yes | — | Yes | **2** |
| cycle_detection | `main()` | `int has_cycle` | No | Vec<Vec> (adj list) vs COO | Yes | **3** |
| dfs | `dfs_check_reachability() -> ...` | `int dfs_check_reachability` | No | Vec<Vec> (adj list) vs COO | Yes | **3** |
| dijkstra | `dijkstra_shortest_paths() ->...` | `void dijkstra_shortest_paths` | Yes | Vec<Vec> (adj list) vs COO | Yes | **2, 3** |
| discrete_logarithm | `discrete_log_naive() -> res:...` | `int discrete_log_naive` | Yes | — | Yes | **2** |
| edmond_karp | `main()` | `int64_t max_flow_value` | Yes | Vec<Vec> (adj list) vs COO | — | **2, 3** |
| fast_exponential | `main()` | `uint64_t exponentiation` | Yes | — | Yes | **2** |
| gcd | `main()` | `uint64_t compute_gcd` | No | — | Yes | **1** |
| house_robber | `main()` | `uint64_t rob` | Yes | — | Yes | **2** |
| insertion_sort | `insertion_sort()` | `void insertion_sort` | No | — | — | **1** |
| integer_exponential | `main()` | `uint64_t exponentiation` | Yes | — | Yes | **2** |
| jump_game | `main()` | `int can_jump` | No | — | — | **1** |
| k_smallest | `main()` | `int quick_select` | No | — | — | **1** |
| kmp | `kmp_search() -> indices: Vec...` | `void kmp_search` | No | — | — | **1** |
| knapsack_01 | `main()` | `uint64_t solve_knapsack_01` | Yes | — | Yes | **2** |
| knapsack_unbounded | `main()` | `uint64_t solve_knapsack_unbo...` | Yes | — | Yes | **2** |
| kruskal | `kruskal_mst() -> edges: Vec<...` | `int kruskal_mst` | Yes | Vec<Vec> (adj list) vs COO | — | **2, 3** |
| lca | `main()` | `N/A` | Yes | Box<Node> tree vs array | Yes | **2, 4** |
| linear_search | `linear_search_lower_bound() ...` | `int linear_search_lower_boun...` | No | — | — | **1** |
| linearsys_gf2 | `main()` | `int solve_linear_system_gf2` | Yes | Vec<Vec> | Yes | **2, 3** |
| llrbt_delete | `main()` | `int llrbt_delete` | Yes | Box<Node> tree vs array | — | **2, 4** |
| llrbt_flipcolor | `main()` | `void flip_colors` | Yes | Box<Node> tree vs array | Yes | **2, 4** |
| llrbt_insert | `main()` | `int llrbt_insert` | Yes | Box<Node> tree vs array | — | **2, 4** |
| llrbt_rotateleft | `main()` | `void fixup_rotate_left` | Yes | Box<Node> tree vs array | — | **2, 4** |
| llrbt_rotateright | `main()` | `void fixup_rotate_right` | Yes | Box<Node> tree vs array | — | **2, 4** |
| longest_common_subsequence | `main()` | `int solve_longest_common_sub...` | No | — | Yes | **1** |
| longest_increasing_subsequence | `longest_increasing_subsequen...` | `int longest_increasing_subse...` | No | — | Yes | **1** |
| longest_palindrome_substring | `longest_palindromic_substrin...` | `void longest_palindromic_sub...` | No | — | — | **1** |
| matrix_multiplication | `matrix_multiply() -> C: Vec<...` | `void matrix_multiply` | Yes | Vec<Vec> | — | **2, 3** |
| max_matching | `max_bipartite_matching() -> ...` | `int max_bipartite_matching` | No | Vec<Vec> (adj list) vs COO | — | **3** |
| maxheap_popmax | `main()` | `N/A` | No | — | — | **1** |
| maxheap_push | `main()` | `void maxheap_push` | No | — | — | **1** |
| maximum_subarray_sum | `main()` | `int64_t max_subarray_sum` | No | — | Yes | **1** |
| merge_sort | `merge_sort()` | `void merge_sort` | No | — | — | **1** |
| polymul_karatsuba | `main()` | `void poly_multiply` | Yes | — | — | **2** |
| polymul_naive | `main()` | `void poly_multiply` | Yes | — | — | **2** |
| prim | `prim_mst() -> edges: Vec<(us...` | `int64_t prim_mst_weight` | Yes | Vec<Vec> (adj list) vs COO | — | **2, 3** |
| push_relabel | `main()` | `int max_flow_value` | Yes | Vec<Vec> (adj list) vs COO | — | **2, 3** |
| queue_dequeue | `main()` | `int dequeue` | No | — | — | **1** |
| queue_enqueue | `main()` | `void enqueue` | No | — | — | **1** |
| quick_sort | `quick_sort()` | `void quick_sort` | No | — | — | **1** |
| ringbuffer_dequeue | `main()` | `int dequeue` | No | — | — | **1** |
| ringbuffer_enqueue | `main()` | `void enqueue` | No | — | — | **1** |
| stack_pop | `main()` | `int pop` | No | — | — | **1** |
| stack_push | `main()` | `void push` | No | — | — | **1** |
| string_search_naive | `main()` | `void naive_search` | No | — | — | **1** |
| trial_division_naive | `main()` | `int check_prime` | No | — | Yes | **1** |
| trial_division_optimized | `main()` | `int check_prime` | No | — | Yes | **1** |

## 3. Soundness probe

Run date: 2026-04-28.
Frama-C 32 (Germanium) + Alt-Ergo 2.6.2 + Z3 4.12.5, `-wp-par 4`.

### 3.1 — WP front-end check (77 / 77 files)

Command: `frama-c -wp -wp-timeout 5 -wp-prover alt-ergo,z3 -wp-par 4 <file>`.

Result: zero `User Error`, zero `[kernel] Failure`, zero unbound-symbol
errors, zero type errors, zero `[wp] Error` lines. The only diagnostics
emitted are `CERT:MSC:37 falls-through` warnings from the empty function
bodies — expected and harmless.

Per-file proof tallies are not meaningful here (most ensures clauses time out
because there is no implementation), but the front-end successfully encodes
every spec into VCs.

### 3.2 — `\false` lemma probe (34 / 34 axiomatic files)

For each file containing an `axiomatic` block, append

```
/*@ lemma soundness_check: \false; */
```

and re-run WP. If the lemma proves, the axioms are inconsistent.

Files probed (34): `bellman_ford`, `bracket_matching`, `coin_change`,
`dijkstra`, `discrete_logarithm`, `edmond_karp`, `fast_exponential`, `gcd`,
`house_robber`, `integer_exponential`, `knapsack_01`, `knapsack_unbounded`,
`kruskal`, `lca`, `linearsys_gf2`, `llrbt_delete`, `llrbt_flipcolor`,
`llrbt_insert`, `llrbt_rotateleft`, `llrbt_rotateright`,
`longest_common_subsequence`, `matrix_multiplication`, `maxheap_popmax`,
`maxheap_push`, `polymul_karatsuba`, `polymul_naive`, `prim`, `push_relabel`,
`rod_cutting`, `segmenttree_build`, `segmenttree_modify`, `segmenttree_query`,
`unionfind_find`, `unionfind_linkroots`.

Result at 10s timeout: **34 / 34 Timeout** (good — WP cannot derive `\false`).

Result at 30s timeout, on the 14 heaviest files (multiple recursive
axiomatics — graph path-weight, DP, polymul, matrix multiplication, lca):
**14 / 14 Timeout**.

### 3.3 — Files without axiomatics (43 files)

The remaining 43 files use only `predicate ... = ...` definitions (no
`axiomatic` blocks). These are structurally sound by construction: predicate
definitions are abbreviations, and all recursive predicates here recurse on
pointer-graph children (`is_bst(t->left)`, etc.), with no negative-occurrence
fixpoints. No probe needed.

### 3.4 — Caveats

1. **Probe timeout is not a soundness proof.** Provers may simply be
   incomplete. A 30s ceiling is a reasonable first-pass sanity check; longer
   runs or alternative provers may reveal what was hidden.
2. **The probe doesn't catch contract over-strength.** It only catches
   `\false`-derivable axioms. A `requires` clause that is unintentionally
   contradictory (so the function is vacuously well-specified for *no* input)
   would not be caught here. Such files would also pass — but the model would
   be unable to find any input satisfying the precondition.
3. **The probe doesn't catch contract under-strength.** A spec that misses an
   important postcondition will pass the probe trivially.

## 4. Reference & next step

- Source corpus: [zak-al/acsl-benchmarks](https://github.com/zak-al/acsl-benchmarks)
  (`algoveri-spec/`).
- Container recipe: `scripts/apptainer_setup/acsl.def` in this fork
  (matches the Frama-C 32 / Alt-Ergo 2.6.2 / Z3 4.12.5 / Why3 1.8.2 / OCaml
  5.2.0 versions of the macOS dev setup).
- Next step: hand the `acsl_spec.c` files to a model with the AlgoVeri 1×15
  budget (one shot, up to 15 repair iterations against `frama-c -wp`), to
  produce the `ALL_PROVED / PARTIAL` table that's directly comparable to
  AlgoVeri's published Dafny / Verus / Lean results.
