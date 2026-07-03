import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSigmaBundle
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentGodement

/-! # mode-3 keystone — the IN-RANGE component core swap (the sigma witness, fully discharged)

`MatchingGodementComponentCoreSwap` asks, at every `MatchingSwapStateConditions`-conditioned state,
for a rename `sigma` fixing `0`, the bottom boundary, and everything above the final counter, that
`MatchingComponentSim`-relates the two transposed Godement run orders.  This file DISCHARGES that
obligation under two additional premises the conditions package does not carry:

  * `CellHasCupCapGenerators` for the three participating cells (the walking-adjunction arities —
    the window-count invariants are stated for cup/cap generators);
  * the window range at the given state (`leftAcc + fLow + gLow ≤ openWires.length` — the
    in-range read discipline).

The witness is `blockRotate shared.nextFresh wA wB` at the post-`cellAlpha` shared state: the
three fixing conjuncts are immediate from `blockRotate_below`/`_above` over the conditions
package (threaded through `cellAlpha`'s run), and the simulation is the shipped
`matchingCoreSwap_componentSim_blockRotate` bundle at the derived shared-state range.

What remains for the UNCONDITIONAL `MatchingGodementComponentCoreSwap` is exactly the premise
gap: showing the soundness chain only ever consumes the residual at states/cells satisfying
the two extra premises (the reachable-boundary discipline), or handling their failure
degenerately — the in-range-discipline brick.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Nat cancellation helper (hand-rolled; the core cancellation lemmas leak `propext`) -/

private theorem natAddLeCancelRight : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled ≤ rightSum + cancelled → leftSum ≤ rightSum
  | 0, _, _, sumsLe => sumsLe
  | cancelled + 1, _, _, sumsLe => natAddLeCancelRight cancelled (Nat.le_of_succ_le_succ sumsLe)

/-! ## The in-range core swap -/

/-- ★ **The component core swap, DISCHARGED under the in-range/cup-cap premises.**  At every
conditioned state whose window is in range, with walking-adjunction arities on the three cells,
the rename `blockRotate shared.nextFresh wA wB` (at the post-`cellAlpha` shared state) fixes `0`,
the bottom boundary, and everything at-or-above the final counter, and
`MatchingComponentSim`-relates the two transposed Godement run orders.  This is the
`MatchingGodementComponentCoreSwap` body with the two premises the conditions package does not
carry made explicit. -/
theorem matchingGodementComponentCoreSwap_ofInRange {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state)
    (alphaLowCupCap : CellHasCupCapGenerators cellAlpha)
    (alphaCupCap : CellHasCupCapGenerators cellAlphaUpper)
    (betaCupCap : CellHasCupCapGenerators cellBeta)
    (windowsInRange : leftAcc.length + fLow.length + gLow.length ≤ state.openWires.length) :
    ∃ sigma : Nat → Nat,
      sigma 0 = 0
        ∧ (∀ identifier, identifier < bottomCount → sigma identifier = identifier)
        ∧ (∀ identifier,
            (runMatchingCell (runMatchingCell
                (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta).nextFresh ≤ identifier
            → sigma identifier = identifier)
        ∧ MatchingComponentSim sigma
            (runMatchingCell (runMatchingCell
                (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta)
            (runMatchingCell (runMatchingCell
                (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                (composePath leftAcc fMid) rightAcc cellBeta)
              leftAcc (composePath gMid rightAcc) cellAlphaUpper) := by
  -- the conditions package at the post-cellAlpha shared state
  have sharedConditions := matchingSwapStateConditions_runMatchingCell bottomCount state leftAcc
    (composePath gLow rightAcc) cellAlpha conditions
  -- the shared-state window range from the given range via cellAlpha's boundary-count invariant
  have rangeAlphaLow : leftAcc.length + fLow.length ≤ state.openWires.length :=
    Nat.le_trans (Nat.le_add_right (leftAcc.length + fLow.length) gLow.length) windowsInRange
  have countAlphaLow := (runMatchingCell_openWiresSuffix_invariant leftAcc
    (composePath gLow rightAcc) cellAlpha state alphaLowCupCap rangeAlphaLow).2
  have sharedRange : leftAcc.length + fMid.length + gLow.length
      ≤ (runMatchingCell state leftAcc (composePath gLow rightAcc)
          cellAlpha).openWires.length := by
    have padded : leftAcc.length + fMid.length + gLow.length + fLow.length
        ≤ (runMatchingCell state leftAcc (composePath gLow rightAcc)
            cellAlpha).openWires.length + fLow.length := by
      rw [countAlphaLow,
        Nat.add_right_comm (leftAcc.length + fMid.length) gLow.length fLow.length,
        Nat.add_right_comm leftAcc.length fMid.length fLow.length,
        Nat.add_right_comm (leftAcc.length + fLow.length) fMid.length gLow.length]
      exact Nat.add_le_add_right windowsInRange fMid.length
    exact natAddLeCancelRight fLow.length padded
  -- the witness: the block rotation at the shared counter
  refine ⟨blockRotate (runMatchingCell state leftAcc (composePath gLow rightAcc)
      cellAlpha).nextFresh (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta),
    blockRotate_below (runMatchingCell state leftAcc (composePath gLow rightAcc)
      cellAlpha).nextFresh (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta) 0
      sharedConditions.nfPos,
    fun identifier belowBottom => blockRotate_below (runMatchingCell state leftAcc
      (composePath gLow rightAcc) cellAlpha).nextFresh (cellFreshCount cellAlphaUpper)
      (cellFreshCount cellBeta) identifier
      (Nat.lt_of_lt_of_le belowBottom sharedConditions.bottomLe),
    ?_,
    matchingCoreSwap_componentSim_blockRotate cellAlphaUpper cellBeta leftAcc rightAcc
      (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
      alphaCupCap betaCupCap sharedConditions.fresh sharedConditions.nfPos
      sharedConditions.forest sharedRange⟩
  -- the fixes-above conjunct: the final counter is the shared counter plus both widths
  intro identifier atOrAboveFinal
  have finalCounterEq : (runMatchingCell (runMatchingCell
        (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
        leftAcc (composePath gLow rightAcc) cellAlphaUpper)
      (composePath leftAcc fHigh) rightAcc cellBeta).nextFresh
      = (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha).nextFresh
        + cellFreshCount cellAlphaUpper + cellFreshCount cellBeta := by
    rw [runMatchingCell_nextFresh (runMatchingCell
        (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
        leftAcc (composePath gLow rightAcc) cellAlphaUpper)
        (composePath leftAcc fHigh) rightAcc cellBeta,
      runMatchingCell_nextFresh (runMatchingCell state leftAcc (composePath gLow rightAcc)
        cellAlpha) leftAcc (composePath gLow rightAcc) cellAlphaUpper]
  exact blockRotate_above (runMatchingCell state leftAcc (composePath gLow rightAcc)
      cellAlpha).nextFresh (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta) identifier
    (finalCounterEq ▸ atOrAboveFinal)

/-! ## Honesty marker -/

/-- **Honesty marker — the component core-swap witness is DISCHARGED under the in-range/cup-cap
premises.**  `matchingGodementComponentCoreSwap_ofInRange`: at every conditioned state whose
window is in range, with walking-adjunction arities on the three cells, the explicit rename
`blockRotate shared.nextFresh wA wB` realises all four conjuncts of the
`MatchingGodementComponentCoreSwap` body — the fixing conjuncts from the conditions package, the
simulation from the shipped `MatchingComponentSim` bundle.  NOT yet covered: the UNCONDITIONAL
`MatchingGodementComponentCoreSwap` (and hence the `fxMode_hasMatchingComponentCoreSwapWitness`
flip) — the soundness chain must be shown to consume the residual only at states/cells satisfying
the two extra premises (the reachable-boundary in-range discipline), or their failure handled
degenerately, alongside the documented empty-boundary case.  `= true`. -/
def fxMode_hasMatchingCoreSwapInRangeWitness : Bool := true

end FX1Poly.Polygraph
