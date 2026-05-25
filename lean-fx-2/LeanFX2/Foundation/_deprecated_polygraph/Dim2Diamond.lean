import LeanFX2.Foundation._deprecated_polygraph.StepLabel

/-! # Dim2Diamond — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


/-! # `Diamond.toDim2Cell` — dim-2 cell embedding (K11.17)

K11.14 ships dim-1 polygraph cells (one per `StepLabel`).  K11.17
lifts the cd_lemma diamond — the Tait-Martin-Löf coherence
witnessing that two parallel reductions join at the same common
reduct — to a dim-2 polygraph cell.

## Diamond as a 2-cell coherence

Given a critical pair of dim-1 cells `lhs, rhs : StepLabel`, the
cd_lemma says: `RawStep.par.cd_lemma` (`RawCdLemma.lean`) produces
a common reduct.  At the polygraph layer this coherence is a
single dim-2 cell

  `PolyCell.cell lhs.toDim1Cell rhs.toDim1Cell 0`

— source = `lhs`'s dim-1 cell, target = `rhs`'s dim-1 cell, idx =
0 (one universal coherence per parallel pair; K11.18 will enumerate
the specific critical-pair instances).

## Why one universal idx = 0?

FX's rewrite system has confluence as a *uniform* property (Church-
Rosser via Tait-Martin-Löf development closure); for any two
parallel reductions, the join exists by the *same* cd-lemma
theorem.  At the polygraph layer this is a single generator
2-cell per (source, target) dim-1 pair, indexed by `0` because
there's no choice of *which* diamond proof to use — it's the
canonical one.

K11.18 distinguishes specific critical-pair instances (when two β
rules overlap on the same redex shape) by enumerating *those*
configurations with non-zero indices.

## Why no `cd_lemma → PolyCell` function?

Same Prop->Type wall as K11.14: `RawStep.par.cd_lemma` is a
`Prop`-valued theorem, and `PolyCell` is `Type`-valued.  The
Type-layer here ships the *generators* of the 2-cell layer
parameterized by their dim-1 boundaries, matching Burroni 1993
§1.1's reading.  The actual cd_lemma proof lives at the Prop
witness layer (`Confluence/CdLemma.lean`); the polygraph cell
records *which* coherence is being applied, not the proof tree.

## What this file ships (zero axioms)

* `Diamond.toDim2Cell : StepLabel -> StepLabel -> PolyCell 2 0 0`
  — uniform parameterized dim-2 embedding.  Consumers pattern-match
  on `PolyCell.cell _ _ 0` directly; no separate unfolding lemma is
  shipped because the body is a single `PolyCell.cell` application
  and adding a `_def`-suffixed `rfl` theorem trips the
  `rfl-on-nontrivial-name` discipline gate (matches precedent for
  `Term.cdRaw_unfolds` / K11.15 `fromIndex?`).

## Root status

`FX-rich` (Layer P substrate underneath Foundation Layer 0).

## Task anchor

K11.17 in the K-series build plan.  Pairs with K11.18 (Squier
critical-pair enumeration: subset of `(lhs, rhs)` StepLabel pairs
with non-trivial overlap), K11.19 (strategy 3-cells over the dim-2
layer composing diamonds).
-/

namespace LeanFX2.Foundation._deprecated_polygraph

/-- The dim-2 diamond cell parameterized by its two dim-1 sides.
Universal coherence: every parallel pair `(lhs, rhs)` gets exactly
one diamond cell `PolyCell.cell lhs.toDim1Cell rhs.toDim1Cell 0`.

The `idx` field is `0` because at the abstract coherence layer
there is only one cd_lemma applicable per parallel pair — FX's
rewrite system is uniformly Church-Rosser, so the diamond is
canonical.  K11.18 will enumerate non-trivial critical-pair
overlaps with non-zero indices. -/
def Diamond.toDim2Cell (leftSide rightSide : StepLabel) : PolyCell 2 0 0 :=
  PolyCell.cell leftSide.toDim1Cell rightSide.toDim1Cell 0

end LeanFX2.Foundation._deprecated_polygraph

-/
