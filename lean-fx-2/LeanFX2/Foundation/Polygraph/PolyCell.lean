/-! # `PolyCell` — universal n-cell type per Burroni 1993 §1.1

Polygraphs (Burroni 1993, Métayer 2008; equivalently computads per
Street 1976) are the canonical data structure for higher-dimensional
rewriting.  An n-cell is an element at dimension `n` in the polygraph;
`(n+1)`-cells carry source and target as `n`-cells.

This file ships the BASE inductive structure.  Source/target/idx
projections + `DecidableEq` are intentionally deferred to K11.2
(`ParallelPair`) and K11.3 (well-foundedness + DecidableEq), where the
parallelism predicate / index-equality motive supplies the
dependent-index witness needed to keep partial-match constructions
propext-clean per `feedback_lean_indexed_partial_match.md`.  This
mirrors the discipline followed by the existing Layer-0 indexed
inductives (`RawTerm`, `Ty`, `Subst`), which likewise defer
`DecidableEq` to surrounding metatheory layers rather than `deriving`
it locally.

Operadic composition + interchange laws land in K11.4-K11.6.  Free
n-category construction in K11.7.

FX adopts the OPERADIC reading per Squier 1987 + Métayer 2008:
1-cells carry multi-port arity `(m, n)`.  This subsumes Lafont-style
interaction nets natively, eliminating the need for a separate
`HyperTerm` IR in the four-encoding grid
(Tree / PolyTerm / ValueTerm / EGraph).

## References

* Burroni 1993, "Higher dimensional word problems with applications to
  equational logic", TCS 115.
* Street 1976, "Limits indexed by category-valued 2-functors", JPAA 8.
* Squier 1987, "Word problems and a homological finiteness condition
  for monoids", JPAA 49.
* Métayer 2003, "Resolutions by polygraphs", TAC 11.

## Root status

`FX-rich` (Layer P substrate underneath Foundation Layer 0).
Promotion to `Bridge` is gated on K19.x `encode_polyterm_sound`
theorems.

## Task anchor

K11.1 in the K-series build plan.  Pairs with K11.2 `ParallelPair`
for projection + parallelism predicate + K11.3 well-foundedness +
K11.7 free n-category construction.
-/

namespace LeanFX2.Foundation.Polygraph

/-- Universal n-cell type indexed by dimension.

A `PolyCell n` is a cell at dimension `n` in some abstract polygraph.
At dim 0 the cell is a bare generator with a `Nat` handle.  At every
higher dimension the cell additionally carries its own source and
target as cells one dimension lower; the `Nat` handle distinguishes
distinct cells sharing the same source/target pair.

The dimension index is computational `Nat` (no propositional equality)
to keep the type `@[reducible]`-friendly per `kernel-metaplan` strict
zero-axiom discipline and to avoid the universe-constructor blocker
documented in `feedback_lean_universe_constructor_block.md`.

Source/target/idx projections live in K11.2; this file ships the
constructors + `DecidableEq` only. -/
inductive PolyCell : Nat → Type
  /-- Dim-0 cell — a polygraph generator. -/
  | gen0 (idx : Nat) : PolyCell 0
  /-- Dim-`(dim+1)` cell with explicit source/target dim-`dim` witnesses. -/
  | genSucc (dim : Nat)
            (source target : PolyCell dim)
            (idx : Nat) :
      PolyCell (dim + 1)
  deriving Repr

end LeanFX2.Foundation.Polygraph
