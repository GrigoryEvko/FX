import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCellSwapFoldGlue

/-! # MODE-COMMUTE r27 — gen past gen at CELL granularity (the cellPastCell base case, cap x cap combo)

## What this ships

The first WHOLE-CELL-SHAPED instance of the disjoint-support commutation: two single-generator
cells in the exact Godement-commute configuration (`cellAlphaUpper` whiskered into the f-region,
`cellBeta` into the g-region, positions PRODUCED BY the whisker accumulators' path lengths — not
assumed), run in either order from a `WellFormedArcState`, are `ArcStepSimCount`-related.

  * `arcGenPastGenSwapSimCount_capCap` — both generators caps (`2 => 0`), carrier
    `blockRotate nextFresh 1 1`, guarded by the r27-sharp three-disequality component condition
    on the two windows' reads (windows `[|leftAcc|, +2)` and `[|leftAcc| + 2, +2)` — ADJACENT, the
    whisker geometry's `gap = 0` instance).

The proof is the full intended `cellPastCell` base-case pipeline, end to end: `runArcCell_gen`
(the cell runs as one atom) -> `stepArcAtom_eq_stepCapArc` (arity dispatch, boundary lengths read
off the whisker paths) -> `ModalityPath.length_composePath` (the position of the g-region atom IS
`|leftAcc| + |fX|`) -> the r27 general cap x cap arm at `gap := 0`.  This DISCHARGES the
position-shift bookkeeping the r26 bill named ("threading the cap-aware position shift") for the
single-atom-cell instance: the `-2` shift is literally `|fHigh| = 0` versus `|fMid| = 2`.

## The honest residual

The remaining three arity combos (cup/cup, cup/cap, cap/cup) are mechanical clones of this
pipeline onto the other three general arms; the multi-atom `atomPastCell -> cellPastCell` double
induction (threading the window geometry and the component guard through intermediate states)
remains the standing delivery.  The pins stay `false`.

Raw Lean 4 + Init; the proof is rewrite plumbing over shipped equations plus one arm instance.
Per-declaration `#assert_no_axioms` + independent `#print axioms` in the twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★ **Gen past gen at CELL granularity, cap x cap combo — the `cellPastCell` base case.**  Two
single-cap cells in the Godement configuration: `genAlpha : fMid => fHigh` fires in the f-region
(window start `|leftAcc|`), `genBeta : gLow => gMid` in the g-region (window start
`|leftAcc| + |fX|`, the whisker-accumulated position — `|fMid| = 2` before `genAlpha` fires,
`|fHigh| = 0` after: the cap-aware `-2` shift, DERIVED from the path lengths).  Both run orders
from a well-formed state are `ArcStepSimCount`-related by `blockRotate nextFresh 1 1`, under the
sharp component guard on the two adjacent windows' reads. -/
theorem arcGenPastGenSwapSimCount_capCap {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath signature.graph middleMode targetMode}
    (genAlpha : signature.twoCell fMid fHigh) (genBeta : signature.twoCell gLow gMid)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (state : ArcWireState) (wellFormed : WellFormedArcState state)
    (hAlphaDomWidth : fMid.length = 2) (hAlphaCodWidth : fHigh.length = 0)
    (hBetaDomWidth : gLow.length = 2) (hBetaCodWidth : gMid.length = 0)
    (window : leftAcc.length + 2 ≤ state.openWires.length)
    (readOneFirstDisjoint :
      isSameComponent state.links (natListGetAt state.openWires leftAcc.length)
        (natListGetAt state.openWires (leftAcc.length + 2)) = false)
    (readOneSecondDisjoint :
      isSameComponent state.links (natListGetAt state.openWires leftAcc.length)
        (natListGetAt state.openWires (leftAcc.length + 2 + 1)) = false)
    (readTwoFirstDisjoint :
      isSameComponent state.links (natListGetAt state.openWires (leftAcc.length + 1))
        (natListGetAt state.openWires (leftAcc.length + 2)) = false) :
    ArcStepSimCount (blockRotate state.nextFresh 1 1)
      (runArcCell
        (runArcCell state leftAcc (composePath gLow rightAcc) (RawTwoCellExpr.gen genAlpha))
        (composePath leftAcc fHigh) rightAcc (RawTwoCellExpr.gen genBeta))
      (runArcCell
        (runArcCell state (composePath leftAcc fMid) rightAcc (RawTwoCellExpr.gen genBeta))
        leftAcc (composePath gMid rightAcc) (RawTwoCellExpr.gen genAlpha)) := by
  -- the whisker-accumulated positions
  have positionHigh : (composePath leftAcc fHigh).length = leftAcc.length := by
    rw [ModalityPath.length_composePath leftAcc fHigh, hAlphaCodWidth]
    rfl
  have positionMid : (composePath leftAcc fMid).length = leftAcc.length + 2 := by
    rw [ModalityPath.length_composePath leftAcc fMid, hAlphaDomWidth]
  -- the redex order runs as two cap steps at (|leftAcc|, |leftAcc|)
  have redexRuns : runArcCell
        (runArcCell state leftAcc (composePath gLow rightAcc) (RawTwoCellExpr.gen genAlpha))
        (composePath leftAcc fHigh) rightAcc (RawTwoCellExpr.gen genBeta)
      = stepCapArc (stepCapArc state leftAcc.length) leftAcc.length := by
    rw [runArcCell_gen, runArcCell_gen,
      stepArcAtom_eq_stepCapArc state
        (SpineAtom.mk sourceMode middleMode leftAcc fMid fHigh genAlpha
          (composePath gLow rightAcc)) hAlphaDomWidth hAlphaCodWidth,
      stepArcAtom_eq_stepCapArc (stepCapArc state leftAcc.length)
        (SpineAtom.mk middleMode targetMode (composePath leftAcc fHigh) gLow gMid genBeta
          rightAcc) hBetaDomWidth hBetaCodWidth]
    show stepCapArc (stepCapArc state leftAcc.length) (composePath leftAcc fHigh).length
      = stepCapArc (stepCapArc state leftAcc.length) leftAcc.length
    rw [positionHigh]
  -- the reduct order runs as two cap steps at (|leftAcc| + 2, |leftAcc|)
  have reductRuns : runArcCell
        (runArcCell state (composePath leftAcc fMid) rightAcc (RawTwoCellExpr.gen genBeta))
        leftAcc (composePath gMid rightAcc) (RawTwoCellExpr.gen genAlpha)
      = stepCapArc (stepCapArc state (leftAcc.length + 2)) leftAcc.length := by
    rw [runArcCell_gen, runArcCell_gen,
      stepArcAtom_eq_stepCapArc state
        (SpineAtom.mk middleMode targetMode (composePath leftAcc fMid) gLow gMid genBeta
          rightAcc) hBetaDomWidth hBetaCodWidth]
    show stepArcAtom (stepCapArc state (composePath leftAcc fMid).length)
        (SpineAtom.mk sourceMode middleMode leftAcc fMid fHigh genAlpha
          (composePath gMid rightAcc))
      = stepCapArc (stepCapArc state (leftAcc.length + 2)) leftAcc.length
    rw [stepArcAtom_eq_stepCapArc (stepCapArc state (composePath leftAcc fMid).length)
        (SpineAtom.mk sourceMode middleMode leftAcc fMid fHigh genAlpha
          (composePath gMid rightAcc)) hAlphaDomWidth hAlphaCodWidth]
    show stepCapArc (stepCapArc state (composePath leftAcc fMid).length) leftAcc.length = _
    rw [positionMid]
  -- the general arm at gap := 0, positions collapsed
  have zeroGapLow : (0 : Nat) + leftAcc.length = leftAcc.length := Nat.zero_add leftAcc.length
  have zeroGapHigh : (0 : Nat) + 2 + leftAcc.length = leftAcc.length + 2 := by
    rw [Nat.zero_add 2, Nat.add_comm 2 leftAcc.length]
  have zeroGapHighSucc : (0 : Nat) + 2 + leftAcc.length + 1 = leftAcc.length + 2 + 1 := by
    rw [zeroGapHigh]
  have armInstance := arcDisjointCapCapSwapSimCount_ofWellFormed state leftAcc.length 0 wellFormed
    window
    (by rw [zeroGapHigh]; exact readOneFirstDisjoint)
    (by rw [zeroGapHighSucc]; exact readOneSecondDisjoint)
    (by rw [zeroGapHigh]; exact readTwoFirstDisjoint)
  rw [zeroGapLow, zeroGapHigh] at armInstance
  rw [redexRuns, reductRuns]
  exact armInstance

/-! ## Honesty marker + pins -/

/-- **Honesty marker — the `cellPastCell` base case is DEMONSTRATED end to end at the cap x cap
combo.**  Positions derived from the whisker accumulators (`ModalityPath.length_composePath` +
the boundary-width hypotheses), the arity dispatch onto the general arm, the `gap = 0` adjacency
of the Godement configuration, and the sharp component guard — the full pipeline the multi-atom
double fold iterates.  The remaining three arity combos are mechanical clones; the multi-atom
fold is the standing delivery.  `= true`. -/
def fxMode_hasGenPastGenCellSwapBaseCase : Bool := true

/-- **Honesty pin — the whole-cell disjoint whisker-support target stays OPEN** (multi-atom
cells).  `rfl`. -/
theorem arcGenPastGenCellSwap_disjointWhiskerSupport_stays_false :
    fxMode_hasDisjointWhiskerSupport = false := rfl

/-- **Honesty pin — residual (2)'s renameable-level marker stays OPEN.**  `rfl`. -/
theorem arcGenPastGenCellSwap_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

/-- **Honesty pin — the partition-commute keystone stays OPEN.**  `rfl`. -/
theorem arcGenPastGenCellSwap_partitionCommute_stays_false :
    fxMode_hasArcPartitionCommuteProof = false := rfl

/-- **Honesty pin — the machine-refuted same-partition-fresh keystone is NEVER flipped.**  `rfl`. -/
theorem arcGenPastGenCellSwap_samePartitionFresh_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
