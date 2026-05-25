/-! # `PolyCell` — globular polygraph cell type (Burroni 1993 §1.1)

A `PolyCell dim sourceVtx targetVtx` is a cell at dimension `dim` in a
globular polygraph whose globular dim-0 boundary is the pair of
vertices `(sourceVtx, targetVtx)`.

## Burroni 1993 parallelism — built into the type

For Burroni 1993 §1.1, an `(n+1)`-cell `c` has source `s_{n+1}(c)` and
target `t_{n+1}(c)` at dim `n`, satisfying the parallelism condition

```text
s_n(s_{n+1}(c)) = s_n(t_{n+1}(c))   and   t_n(s_{n+1}(c)) = t_n(t_{n+1}(c)).
```

The globular interpretation: every cell has a unique `(sourceVtx,
targetVtx)` pair at dim 0 (its globular boundary), and the parallelism
condition is the statement that `s_{n+1}(c)` and `t_{n+1}(c)` share
their globular boundary.  By indexing `PolyCell` on this dim-0
boundary, we make parallelism INTRINSIC — the constructor for a
dim-`(n+2)` cell requires its source and target to be presented at the
SAME boundary `(sourceVtx, targetVtx)`, which is exactly Burroni's
parallelism condition lifted to the type level.

## Three constructors covering dim 0, 1, and ≥ 2

* `atom vtx` — a dim-0 cell at vertex `vtx`; its own boundary is the
  trivial loop `(vtx, vtx)`.
* `arrow source target idx` — a dim-1 cell from a dim-0 atom at
  `sourceVtx` to a dim-0 atom at `targetVtx`.  These dim-0 atoms can
  inhabit different vertices; the resulting 1-cell carries the pair
  as its globular boundary.
* `cell source target idx` — a dim-`(dim+2)` cell between two
  dim-`(dim+1)` cells `source` and `target` that share globular
  boundary `(sourceVtx, targetVtx)`.  Parallelism is enforced by the
  type indices.

## What is NOT in this file

* Source / target / idx projections.  K11.2 (`ParallelPair`) lands the
  projection functions plus a separate `ParallelPair source target`
  predicate witnessing that two parallel cells of the same dim share
  globular boundary at the dim-0 level (a stronger separate statement
  about specific instances; the constructor only enforces it at the
  ambient cell's level).  Projections live there because they require
  the `casesOn`-with-index-equality recipe from
  `feedback_lean_indexed_partial_match.md`.
* `DecidableEq`.  Auto-derivation leaks `propext` on the over-
  constrained per-ctor index shape (`dim=0` / `dim=1` /
  `dim=dim+2`) — this is the indexed-inductive partial-match trap
  from `feedback_lean_indexed_partial_match.md` reaching the
  auto-derived equation lemmas.  K11.3.B ships a hand-rolled
  propext-free instance via `Foundation/Polygraph/DecEq.lean`,
  using `Σ'`-typed cell-decomposition + dim-stratified dispatch.
* Vertical / horizontal composition.  K11.4 / K11.5.
* Multi-port arity (Squier 1987 / Métayer 2008 operadic reading).
  The globular fragment shipped here is single-port — `source` and
  `target` are each a single cell, not a list of ports.  Multi-port
  arity arrives with K11.5's horizontal composition, generalizing the
  globular structure to operadic.  The K11.1 file deliberately ships
  the globular fragment because every FX construct that consumes a
  polygraph cell — `Step.toDim1Cell`, `cd_lemma.toDim2Cell`, strategy
  3-cells — is globular at its boundary.

## References

* Burroni 1993, "Higher dimensional word problems with applications to
  equational logic", TCS 115.
* Street 1976, "Limits indexed by category-valued 2-functors", JPAA 8.
* Squier 1987, "Word problems and a homological finiteness condition
  for monoids", JPAA 49 (operadic reading — applied in K11.5).
* Métayer 2003, "Resolutions by polygraphs", TAC 11.

## Root status

`FX-rich` (Layer P substrate underneath Foundation Layer 0).
Promotion to `Bridge` is gated on K19.x `encode_polyterm_sound`
theorems.

## Task anchor

K11.1 in the K-series build plan.  Pairs with K11.2 `ParallelPair` for
projections + the explicit parallel-pair predicate, K11.3
well-foundedness + DecidableEq, K11.4-K11.5 composition, K11.6
interchange laws, K11.7 free n-category construction.
-/

namespace LeanFX2.Foundation._deprecated_polygraph

/-- Globular polygraph cell at dimension `dim`, with globular dim-0
boundary `(sourceVtx, targetVtx)`.

Three constructors handle the strata:

* `atom` for dim-0 cells (boundary is a trivial self-loop).
* `arrow` for dim-1 cells (carrier of two possibly-distinct vertices).
* `cell` for dim-`(dim+2)` cells (parallelism enforced via shared
  boundary indices on the source/target arguments).

Parallelism is INTRINSIC: a dim-`(n+2)` cell built via `cell` REQUIRES
its source and target to live at the same boundary, so the Burroni
parallelism condition holds automatically at the type level. -/
inductive PolyCell : (dim sourceVtx targetVtx : Nat) → Type
  /-- A dim-0 cell at vertex `vtx`. -/
  | atom (vtx : Nat) : PolyCell 0 vtx vtx
  /-- A dim-1 cell (arrow) from an atom at `sourceVtx` to an atom at
  `targetVtx`.  The dim-0 source and target are presented explicitly
  so that downstream cell-walking machinery can recurse uniformly. -/
  | arrow {sourceVtx targetVtx : Nat}
          (source : PolyCell 0 sourceVtx sourceVtx)
          (target : PolyCell 0 targetVtx targetVtx)
          (idx : Nat) :
      PolyCell 1 sourceVtx targetVtx
  /-- A dim-`(dim+2)` cell whose source and target are dim-`(dim+1)`
  cells sharing globular boundary `(sourceVtx, targetVtx)`.  The
  parallelism condition is enforced by the shared boundary indices on
  the `source` and `target` arguments. -/
  | cell {dim sourceVtx targetVtx : Nat}
         (source target : PolyCell (dim + 1) sourceVtx targetVtx)
         (idx : Nat) :
      PolyCell (dim + 2) sourceVtx targetVtx
  deriving Repr

end LeanFX2.Foundation._deprecated_polygraph
