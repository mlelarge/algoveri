# ACSL benchmark improvements — manifest

This document lists every per-problem change made to the ACSL track of
the AlgoVeri benchmark relative to the original transcription.

## Summary

- **77 / 77** `acsl_nl.txt` files added (one per problem).
- **24 / 77** `acsl_spec.c` files patched to fix translation defects.
  All other specs (53) are unchanged from the original.

The defects fall into four categories: missing `\separated` clauses
(20), operator-precedence bug (1), false postcondition (1), and
multi-pointer separation chains (graph CSR + parallel output arrays —
several files in this category).

## Per-problem spec changes

### Missing `\separated` (Verus-`&mut` translation defect)

In Verus, `&mut` references are guaranteed disjoint by the borrow
checker. The translation to C lost that guarantee, so several specs
left the assumption implicit. Frama-C/WP's default `Typed` memory
model assumes any two same-typed pointers may alias, so the resulting
specs are not provable. The fix is to add `\separated` precondition(s).

| Problem | What was added |
|---|---|
| ac_automata | `\separated` between `out_pids`, `out_idxs`, `haystack`, `pat_lens` |
| bellman_ford | `\separated` between `dist`, `reachable`, and graph CSR (`g`, `g->row_ptr`, `g->col_idx`, `g->col_weight`) |
| bipartite_check | `\separated` between `colors` and graph (`g`, `g->row_ptr`, `g->col_idx`) |
| dijkstra | `\separated(dist + (0..n-1), reachable + (0..n-1))` |
| kmp | `\separated(out_len, out_indices + (0..hay_len))` |
| kruskal | `\separated` among `out_u`, `out_v`, `out_w` (parallel output arrays) |
| linearsys_gf2 | `\separated` between `x_out` and inputs `a`, `b` |
| longest_palindrome_substring | `\separated(out_start, out_len, s + (0..n-1))` |
| matrix_multiplication | `\separated(c, a)`, `\separated(c, b)` |
| maxheap_popmax | `\separated(a + (0..*len-1), len)` |
| polymul_karatsuba | `\separated(out, a)`, `\separated(out, b)` |
| polymul_naive | `\separated(out, a)`, `\separated(out, b)` |
| prim | `\separated` chain among 3 output arrays + graph internals |
| push_relabel | `\separated(f, g, g->row_ptr)` |
| queue_dequeue | `\separated(data + (0..*len-1), len)` |
| queue_enqueue | `\separated(data + (0..cap-1), len)` |
| ringbuffer_dequeue | `\separated(head, len, data + (0..cap-1))` |
| ringbuffer_enqueue | `\separated(head, len, data + (0..cap-1))` |
| stack_pop | `\separated(len, data + (0..cap-1))` |
| stack_push | `\separated(len, data + (0..cap-1))` |
| string_search_naive | `\separated(out_len, out + (0..hay_len))` |
| unionfind_linkroots | `\separated(uf->parent + (0..n-1), uf->rank + (0..n-1))` (guarded by `n == 0` for the empty case) |

### Operator-precedence bug

| Problem | Change |
|---|---|
| sieve_method | `\forall i; 0 <= i < n ==> (primes[i] != 0) <==> is_prime(i)` → `\forall i; 0 <= i < n ==> ((primes[i] != 0) <==> is_prime(i))`. The original parses as `(... ==> primes[i] != 0) <==> is_prime(i)` because `<==>` binds looser than `==>`, making the outer formula equivalent to `is_prime` everywhere unconditionally. |

### False / over-strong postcondition

| Problem | Change |
|---|---|
| k_smallest | The `is_kth_smallest{L1,L2}` predicate required the array at `L2` to be fully sorted. Quick-select does not fully sort — it only partitions. The ACSL transcription was stricter than the Verus original, which existentially quantifies over a sorted permutation. Replaced with `is_kth_smallest{L}(...)` existentially quantified over a phantom `int32_t *b` sorted buffer that has the same multiset as `a`. Added helper predicates `sorted_buffer{L}` and `same_multiset_buf{L}`. |

## Defects flagged in `acsl_nl.txt` rather than fixed

Several specs have problems that are not pure translation bugs but
are *known structural challenges* for ACSL/WP. These are documented
in the `acsl_nl.txt` so a future evaluation can see the obstacle
clearly, but the spec itself is unchanged (changing it would cross
the line into "what the benchmark is testing").

- **llrbt_delete, llrbt_flipcolor, llrbt_insert, llrbt_rotateleft,
  llrbt_rotateright** — `assigns \nothing` paired with structural
  mutation (color toggle, link rebuild) is structurally
  unsatisfiable in WP. The contracts demand a functional-rebuild
  style that WP's allocation model cannot fully express. Flagged in
  each `acsl_nl.txt` as "may require re-spec / weakened assigns
  clause" rather than fixed.
- **lca** — depth-maximality ensures requires structural induction
  with no built-in support; flagged as research-grade.
- **kruskal** (post-`\separated` fix), **prim**, **edmond_karp**,
  **push_relabel**, **scc_tarjan**, **rod_cutting**,
  **knapsack_unbounded**, **knapsack_01** — graph/DP optimality
  goals (Berge's lemma, MST cut property, max-flow min-cut, DP
  upper bound) require top-level lemmas the rules forbid. Flagged.
- **trie_insert, trie_delete, trie_search**, **bst_insert,
  bst_delete**, **splaytree_splay**, **ternarysearchtree_***,
  **segmenttree_build, segmenttree_modify** — recursive structural
  rebuild with malloc and `assigns \nothing` interact poorly with
  WP's incomplete allocation model (`\fresh` "not yet implemented").
  Flagged.
- **discrete_logarithm** — the `acsl_spec.c` itself is correct, but
  `acsl_nl.txt` calls out the C-truncating-vs-Euclidean `%` pitfall
  that user-side modular-arithmetic lemmas often run into (the
  `(x-p) % p == x % p` pattern is true for `p <= x < 2*p` but false
  for `0 <= x < p` in ACSL, opposite of the Verus version).

## Format of `acsl_nl.txt`

Each file follows the gcd / string_search_naive template:

1. Opening sentence: "Your task is to implement [...] and verify its
   functional correctness in ACSL using Frama-C/WP."
2. Algorithmic content (same as `verus_nl.txt`).
3. C-typed signature (uint64_t for u64, pointer + length for Vec<int>,
   pointer parameter for `&mut`).
4. List of verification challenges.
5. ACSL-specific notes paragraph covering:
   - axiomatic preamble structure
   - `loop variant` for termination
   - any required `\separated` clauses
   - `-wp-model Typed` (default) sufficiency
   - modular-arithmetic gotchas
   - the no-top-level-lemmas rule

Word counts: 270 (gcd, simplest) to 579 (llrbt_delete, most
constraint discussion) — mean ≈ 425 words.

## Verification

All 77 `acsl_spec.c` files parse cleanly under `frama-c -wp -wp-no-rte`
(no parse / typecheck errors). Files modified for translation defects
remain in scope for the original verification objective.
