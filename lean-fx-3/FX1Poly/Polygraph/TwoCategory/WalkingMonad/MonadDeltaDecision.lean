import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerEmbedding
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaReps

/-! # WalkingMonad — the Δ decision: the Godement/`ofFull` case FINISHES `mapEqOfConv`

`WalkingMonad/MonadWhiskerEmbedding` reduced the soundness leg `mapEqOfConv` to a single owed case: the `ofFull`
(Godement / interchange) constructor of `MonadSaturatedTwoCellConv`.  This file discharges it — the CAP-FREE analog
of the walking-adjunction keystone's block-transpose invariance.  On Δ the walking monad has NO cap and NO counit,
so the two horizontally-independent middle blocks of an interchange redex act on DISJOINT position windows and their
ordinal-sum embeddings COMMUTE (with the width-delta shift built into the shipped `embedLocalMap` region algebra).

## What this file ships (each piece zero-axiom)

  * **`embedLocalMap_mapsInto`** — the ordinal-sum embedding lands in the summed ordinal (region-wise bound).
  * ★ **`monadMonotoneMapOf_hcomp`** — the horizontal composite's map is the two-whisker `composeMap` of the
    ordinal-sum embeddings (`hcomp` is `whiskerRight` then `whiskerLeft`; the vcomp homomorphism + the two whisker
    embeddings assemble it).
  * ★ **`embedLocalMap_disjointCommute`** — the DISJOINT-WINDOW two-block commute: an f-region block (right-context
    varying) and a g-region block (left-context varying) COMMUTE under `composeMap`, the width-delta shift absorbed
    by `embedLocalMap`'s region split.  This is the cap-free heart the orchestrator named.
  * ★ **`monadMonotoneMapOf_interchange`** — the Godement invariance of the fold: `map (hcomp (α⊟α') (β⊟β'))
    = map (vcomp (hcomp α β) (hcomp α' β'))`, via `monadMonotoneMapOf_hcomp` + `embedLocalMap_composeMap` (split the
    inner composites) + `composeMap_middleSwap` (reassociate) + `embedLocalMap_disjointCommute` (the swap itself).
  * ★★ **`monadMonotoneMapOf_mapEqOfConv`** — the COMPLETE soundness leg: `MonadSaturatedTwoCellConv` cells have
    equal monotone maps.  Structural induction: `ofFull` via the interchange invariance + the spine-invariant
    whisker-functoriality cases; the three laws by the seed lemmas; the four congruences by the shipped congruence
    lemmas; refl/symm/trans trivially.  This FINISHES `mapEqOfConv` — the NO-direction of the Δ decision.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (cons-only lists,
pointwise `listExtById`, hand arithmetic, `composeMap_assoc`).  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The Δ-decision fold-support (relocated to `MonadSaturatedDeltaReps`)

The conv-FREE Godement/interchange fold-support (`mapsInto_mono`, `embedLocalMap_mapsInto`,
`monadMonotoneMapOf_hcomp`, `embedLocalMap_disjointCommute`, `composeMap_middleSwap`,
`monadMonotoneMapOf_interchange`, and the free-conv soundness legs `monadMonotoneMapOf_eqOfStep` /
`_eqOfConv` / `_eqOfConvFull`) is relocated VERBATIM (MONAD-R7 r4) to the bespoke-free deep bridge
`MonadSaturatedDeltaReps`.  The conv-BEARING `mapEqOfConv` induction below (which inducts on the bespoke
`MonadSaturatedTwoCellConv`) STAYS here, threading the relocated legs through the bridge. -/

/-- ★★ **The COMPLETE soundness leg `mapEqOfConv`.**  Every `MonadSaturatedTwoCellConv` derivation preserves the
monotone map: `ofFull` via `monadMonotoneMapOf_eqOfConvFull` (Godement invariance + spine-invariant whisker
functoriality); the three monad laws by the seed lemmas; the four congruences by the shipped congruence lemmas;
refl/symm/trans trivially.  This is the NO-direction of the walking-monad Δ decision. -/
theorem monadMonotoneMapOf_mapEqOfConv {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : MonadSaturatedTwoCellConv cellA cellB) :
    monadMonotoneMapOf cellA = monadMonotoneMapOf cellB := by
  induction conv with
  | ofFull h => exact monadMonotoneMapOf_eqOfConvFull h
  | leftUnit => exact monadMonotoneMapOf_leftUnit_eq_id
  | rightUnit => exact monadMonotoneMapOf_rightUnit_eq_id
  | assoc => exact monadMonotoneMapOf_assoc_eq
  | vcompCongrLeft cellBeta _ ih => exact monadMonotoneMapOf_vcompCongrLeft cellBeta ih
  | vcompCongrRight cellAlpha _ ih => exact monadMonotoneMapOf_vcompCongrRight cellAlpha ih
  | whiskerLeftCongr oneCell _ ih => exact monadMonotoneMapOf_whiskerLeftCongr oneCell ih
  | whiskerRightCongr oneCell _ ih => exact monadMonotoneMapOf_whiskerRightCongr oneCell ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The soundness leg `mapEqOfConv` is COMPLETE: the Godement / `ofFull` residual is discharged by
`monadMonotoneMapOf_interchange` (the disjoint-window two-block commute, cap-free on Δ), and the full induction
`monadMonotoneMapOf_mapEqOfConv` assembles it with the shipped law + congruence legs.  What remains toward inhabiting
`MonadSaturatedCanonicalization` is the COMPLETENESS `convOfMapEq` (the EZ staircase).  `= true`. -/
def fxMonad_hasMapEqOfConvComplete : Bool := true

end FX1Poly.Polygraph
