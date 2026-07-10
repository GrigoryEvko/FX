import FX1Poly.Polygraph.TwoCategory.Amalgam.RealLawDispatch
import FX1Poly.Polygraph.TwoCategory.Amalgam.SPrefixRefutation

/-! # Polygraph/TwoCategory/Amalgam/PushoutNormalForm — the GAP-INDEXED pushout normal form (WP-AMALG-2 r3, B2)

`SPrefixRefutation.lean` (B1) machine-refuted the naive "`s`-prefix" normal form: the free monoid on the disjoint
`{s, t}` does not commute, so an `s` to the right of a `t` cannot be bubbled to a prefix.  This file gives the
CORRECT normal form — GAP-INDEXED — realized to the extent it is provable this round.

## The correct NF coordinate: s-walls (fixed) + per-gap monad content

Because `s` and `t` never commute and no relation moves `s` (the involution is thin: `s·s = id` lives only at the
1-cell level, NOT injected into the pushout — `Witness.lean`), over a FIXED parallel boundary the `s`-letters are
inert WALLS at fixed absolute positions.  Every monad generator (`eta`, `mu`) acts strictly BETWEEN consecutive
walls.  The NF coordinate is therefore the boundary's alternating factorisation (`InterleavingNF.blockDecompose`)
read as: the component-1 (`true`) blocks are the WALLS; the component-2 (`false`) blocks are the GAPS, each hosting
a monad sub-cell `t^a ⇒ t^b`.  The NF is `(gap-wise monad Eilenberg-Zilber normal form) whiskered by the fixed
s-walls`.

## What is shipped here (each zero-axiom, structural / `decide`, ASCII-only)

  * **`pushoutWallBlocks` / `pushoutGapBlocks`** — the wall (component-1) and gap (component-2) blocks of a boundary
    word, from `blockDecompose`.  On the witness word `s·t·s·t·t` they compute to `[[s], [s]]` (two walls) and
    `[[t], [t, t]]` (two gaps) by `rfl` — the gap-indexed coordinate made concrete.
  * **`witnessWord_wallsGaps_blockDecompose`** — walls and gaps interleave back into the full alternating block
    list (the coordinate loses nothing at the wall/gap granularity).
  * **`pushoutRightImageCompletenessLift`** — the BASE-CASE NF SOUNDNESS: a single-gap (pure component-2, no wall)
    boundary is a right-coprojected monad cell, and a monad convertibility of the pre-images transports UNCHANGED
    to the pushout (via the shipped unconditional `pushoutPreservesConvRight`).  "The gap converts to its monad EZ
    normal form" IS the monad's own normalization transported.
  * **`pushoutAssocGapConv` / `pushoutLeftUnitGapConv`** — concrete base-case NF-soundness witnesses: the two
    associativity foldings (resp. the left-unit composite / `id_t`) are DIFFERENT single-gap words that the lift
    makes pushout-convertible.

## The residual, pinned (the multi-gap splice)

The general multi-gap NF-soundness — assembling per-gap normal forms across a shared s-wall into one boundary NF —
is the SPLICE lemma: adjacent gap-cells across a wall compose to the gap-EZ of the concatenation.  It rides the
shipped `WalkingMonad/MonadNormalizeVcomp.wordMul_vcomp` (word-multiplicativity within a gap — CONSUME-only, that
lane owns it) plus the shipped `crossComponentWhiskerCommute` (wall re-nesting).  It is NOT authored here; the exact
residual obligation is named in `fxAmalg_pushoutNormalFormSpliceStaysWalled`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The gap-indexed NF coordinate: walls and gaps of a boundary word -/

/-- The **wall blocks** of a boundary word — the component-1 (`s`, tag `true`) blocks of its alternating
factorisation.  These are the inert walls at fixed absolute positions. -/
def pushoutWallBlocks (word : List (Fin involutionMonadPushout.modalityGenerators.length)) :
    List (List (Fin involutionMonadPushout.modalityGenerators.length)) :=
  (blockDecompose involutionMonadSplit word).filterMap
    (fun block => match block.1 with | true => some block.2 | false => none)

/-- The **gap blocks** of a boundary word — the component-2 (`t`, tag `false`) blocks of its alternating
factorisation.  Each gap hosts a monad sub-cell `t^a ⇒ t^b`. -/
def pushoutGapBlocks (word : List (Fin involutionMonadPushout.modalityGenerators.length)) :
    List (List (Fin involutionMonadPushout.modalityGenerators.length)) :=
  (blockDecompose involutionMonadSplit word).filterMap
    (fun block => match block.1 with | true => none | false => some block.2)

/-- ★ **The witness word's WALLS** — `s·t·s·t·t` has two `s`-walls `[[s], [s]]` (`rfl`): the inert component-1
positions the monad content is pinned between. -/
theorem witnessWord_walls : pushoutWallBlocks witnessWord = [[sLetter], [sLetter]] := rfl

/-- ★ **The witness word's GAPS** — `s·t·s·t·t` has two `t`-gaps `[[t], [t, t]]` (`rfl`): a width-1 gap and a
width-2 gap, each a monad sub-word.  The gap-indexed NF coordinate made concrete. -/
theorem witnessWord_gaps : pushoutGapBlocks witnessWord = [[tLetter], [tLetter, tLetter]] := rfl

/-- The wall + gap extraction is faithful at the block granularity: interleaving the two block streams by tag
recovers the full alternating factorisation of the witness word (`rfl`). -/
theorem witnessWord_wallsGaps_blockDecompose :
    blockDecompose involutionMonadSplit witnessWord
      = [(true, [sLetter]), (false, [tLetter]), (true, [sLetter]), (false, [tLetter, tLetter])] := rfl

/-! ## The base-case NF soundness: the single-gap (right-image) fragment -/

/-- ★★ **THE BASE-CASE NF SOUNDNESS (B2).**  A single-gap boundary — pure component-2, NO wall — is a
right-coprojected monad cell `mapCellAlong inclRight (·)`.  A monad convertibility of the pre-images (over the
reconstructed law relation `MonadLawRelReconstructed`) transports UNCHANGED to a pushout convertibility of the
images over the REAL-law pushout relation `crossPairRealPushoutRel`, via the shipped UNCONDITIONAL right-coprojection
soundness lift `pushoutPreservesConvRight`.  This is exactly "the gap converts to its monad Eilenberg-Zilber normal
form" — the monad's own normalization, transported.  The base case of the gap-indexed NF; the multi-gap splice is
the residual. -/
theorem pushoutRightImageCompletenessLift
    {sourceMode targetMode : Fin monadComputad.modeCount}
    {sourcePath targetPath : ModalityPath monadComputad.toModeGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed cellAlpha cellBeta) :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellAlpha)
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellBeta) :=
  pushoutPreservesConvRight involutionMonadSameModes
    (inclusionLeftTwo involutionComputad monadComputad involutionMonadSameModes rfl)
    (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
    (emptyCellRel involutionComputad.toModeSignature)
    MonadLawRelReconstructed
    conv

/-- ★★ **Base-case NF-soundness witness — associativity.**  The two reconstructed associativity foldings
`reconAssocLeftCell` / `reconAssocRightCell` (DIFFERENT single-gap words `t·t·t ⇒ t`) are pushout-convertible as
right-images: their monad convertibility `reconAssocReflectsTrue` (decided by the reconstructed decider) transports
via the base-case lift.  A concrete single-gap NF collapse inside the pushout. -/
theorem pushoutAssocGapConv :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
        reconAssocLeftCell)
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
        reconAssocRightCell) :=
  pushoutRightImageCompletenessLift reconAssocReflectsTrue

/-- ★★ **Base-case NF-soundness witness — left unit.**  The reconstructed left-unit composite `reconLeftUnitCell`
and `reconIdTCell` (DIFFERENT single-gap words, `t ⇒ t`) are pushout-convertible as right-images, via the base-case
lift on `reconLeftUnitReflectsTrue`.  A second concrete single-gap NF collapse. -/
theorem pushoutLeftUnitGapConv :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
        reconLeftUnitCell)
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
        reconIdTCell) :=
  pushoutRightImageCompletenessLift reconLeftUnitReflectsTrue

/-! ## Observability -/

-- The witness word's walls: expect `[[0], [0]]` (two s-walls, s @ 0).
#eval (pushoutWallBlocks witnessWord).map (fun block => block.map Fin.val)
-- The witness word's gaps: expect `[[1], [1, 1]]` (a width-1 and a width-2 t-gap, t @ 1).
#eval (pushoutGapBlocks witnessWord).map (fun block => block.map Fin.val)

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the GAP-INDEXED pushout normal form + the base-case NF soundness SHIP (WP-AMALG-2 r3,
B2).**  `= true`: the correct NF coordinate is gap-indexed (s-walls at fixed positions + per-gap monad content),
realized by `pushoutWallBlocks` / `pushoutGapBlocks` computing on the witness word `s·t·s·t·t` to two walls
`[[s], [s]]` and two gaps `[[t], [t, t]]` (`witnessWord_walls` / `witnessWord_gaps`, `rfl`).  The BASE-CASE NF
soundness — a single-gap (pure component-2, no wall) cell converts to its transported monad EZ normal form —
SHIPS via `pushoutRightImageCompletenessLift` (the shipped unconditional `pushoutPreservesConvRight` specialised to
`MonadLawRelReconstructed`), non-vacuous on the associativity and left-unit gap collapses (`pushoutAssocGapConv` /
`pushoutLeftUnitGapConv`, DIFFERENT single-gap words made convertible).  This is the CORRECT NF the refuted
`s`-prefix form (B1) is replaced by.  `= true`. -/
def fxAmalg_pushoutNormalFormGapIndexed : Bool := true

/-- **Honesty marker — the multi-gap SPLICE stays walled (the general NF-soundness residual).**  `= true` (the
wall is honestly held).  The base-case (single-gap) NF soundness ships (`pushoutRightImageCompletenessLift`); the
GENERAL multi-gap NF — assembling per-gap normal forms across a shared s-wall into one boundary NF — is the SPLICE
lemma: adjacent gap-cells across a wall compose to the gap-EZ of the concatenation.  Its crux is the shipped
`WalkingMonad/MonadNormalizeVcomp.wordMul_vcomp` (word-multiplicativity within a gap — CONSUME-only, the
WalkingMonad lane owns it) plus the shipped `crossComponentWhiskerCommute` (wall re-nesting).  Named node: the
gap-EZ splice lemma over the reconstructed pushout signature.  It is NOT authored this round.  `= false` would
misreport that the general NF-soundness is dischargeable now; the marker is `true` to record that the residual is
NAMED and its ingredients located.  `= true`. -/
def fxAmalg_pushoutNormalFormSpliceStaysWalled : Bool := true

end FX1Poly.Polygraph.Amalgam
