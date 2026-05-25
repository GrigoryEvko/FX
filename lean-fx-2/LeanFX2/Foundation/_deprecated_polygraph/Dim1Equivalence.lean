import LeanFX2.Foundation._deprecated_polygraph.Dim1Extraction

/-! # `StepLabel ⇌ Dim1Cell` equivalence (K11.16)

K11.14 ships `StepLabel.toDim1Cell` (forward map into the dim-1
polygraph layer).  K11.15 ships `Dim1Cell.toStepLabel?` (partial
inverse, decoding the `idx` field).  This file closes the loop with
the roundtrip theorem witnessing that the two maps are inverse on
the image — every `StepLabel` survives the round-trip exactly.

## Per-Squier 1-polygraph semantics

Squier 1987 reads a 1-polygraph as a finitely-presented (over a
monoid / one-sorted theory) set of generators-plus-relations.  The
equivalence theorem here makes precise that FX's reduction relation,
restricted to the rewrite-generator layer, IS such a polygraph: 110
generators in bijection with the `StepLabel` enumeration, mapped
identity-preservingly to `PolyCell 1 0 0` cells distinguished by
their numeric `idx`.

`StepLabel.fromIndex?_index` is the lower-level lemma: every label's
canonical `index` is decoded back to that same label.  The
high-level `Dim1Cell.toStepLabel?_toDim1Cell` composes `cellIdx`
reduction with `fromIndex?_index` to state the polygraph-level
roundtrip directly on `PolyCell` values.

## Proof shape

Both theorems destruct on the 110-ctor `StepLabel` enumeration and
discharge each case via `rfl` — `cellIdx (PolyCell.arrow _ _ idx)`
reduces to `idx` definitionally, and `fromIndex?` on a literal
0..109 Nat reduces to the matching `some StepLabel.<ctor>` arm.

Per `feedback_lean_match_propext_recipe.md`, `<;> rfl` over a
≤92-case enum stays propext-clean; the 110-case extension here
relies on the same property (no wildcards in `fromIndex?` ctor arms;
the single `_ => none` arm is on Nat, not on `StepLabel`).

## Root status

`FX-rich` (Layer P substrate underneath Foundation Layer 0).

## Task anchor

K11.16 in the K-series build plan.  Direct downstream consumer:
K11.17 `cd_lemma.toDim2Cell` — the dim-2 embedding refers to dim-1
cells via the same `idx`-based encoding and relies on the
equivalence to thread typed rewrite-rule names through the
polygraph layer.
-/

namespace LeanFX2.Foundation._deprecated_polygraph

/-- The numeric index of every `StepLabel` is decoded back to that
exact label by `fromIndex?`.  Single-shot `cases label <;> rfl` —
each of the 110 arms reduces both sides to `some StepLabel.<ctor>`
definitionally. -/
theorem StepLabel.fromIndex_index (label : StepLabel) :
    StepLabel.fromIndex? label.index = some label := by
  cases label <;> rfl

/-- The polygraph-level roundtrip: `Dim1Cell.toStepLabel?` recovers
the exact label that `toDim1Cell` embedded.  Proof reduces
`cellIdx` on the `arrow`-shape cell and then applies
`fromIndex_index`. -/
theorem Dim1Cell.toStepLabel?_toDim1Cell (label : StepLabel) :
    Dim1Cell.toStepLabel? label.toDim1Cell = some label := by
  cases label <;> rfl

end LeanFX2.Foundation._deprecated_polygraph
