This folder contains the AlgoVeri benchmark. Each folder represents a task. Inside each folder, there are 8 files:
+ dafny_nl.txt: natural language description of the problem for Dafny evaluation
+ dafny_spec.dfy: formal specification written in Dafny
+ verus_nl.txt: natural language description of the problem for Verus evaluation
+ verus_spec.rs: formal specification written in Verus
+ lean_nl.txt: natural language description of the problem for Lean evaluation
+ lean_spec.lean: formal specification written in Lean
+ acsl_nl.txt: natural language description of the problem for ACSL/Frama-C-WP evaluation
+ acsl_spec.c: formal specification written in ACSL (annotations on a C function stub)

## ACSL track notes

The ACSL track was added after the original Dafny/Verus/Lean set. The
`acsl_nl.txt` files are ACSL-specific adaptations of the Verus prompt:
same algorithm and verification challenges, but with C signatures
(uint64_t, pointer + length pairs) and ACSL-specific gotchas called
out — default `-wp-model Typed` memory model, C-truncating `%`,
required `loop variant` for termination, `\separated` requirements
where Verus's `&mut` references implied disjointness, and the
benchmark-rule prohibition on top-level lemmas/axioms in the user's
solution.

Several `acsl_spec.c` files were patched to fix translation defects
inherited from Verus (where `&mut` made a non-aliasing assumption
implicit). The patches add `\separated` preconditions or, in one case
(`k_smallest`), restructure a postcondition that demanded a
fully-sorted output where the original Verus version didn't. See
`improvements_manifest.md` in this directory for the full list.
