import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # mode-3 keystone — fresh-shift equivariance of the matching fold's wire view

The block-swap witness `sigma = blockRotate nf wA wB` must relate the open wires of the two transposed
Godement run orders: order-1 runs the upper-alpha block at counter `nf` and the beta block at `nf + wA`;
order-2 runs beta at `nf` and upper-alpha at `nf + wB`.  The SAME cell run from the SAME window contents at
a counter shifted by `delta` produces the SAME wire list up to `freshShiftAbove threshold delta` — old ids
(below the threshold) survive untouched, fresh ids come out exactly `delta` higher.  This file proves that
equivariance for the WIRE VIEW (`openWires` + `nextFresh`): per cup/cap atom, then for a whole block by the
same structural cell induction as `runMatchingCell_openWiresSuffix_invariant`.

Honest scope: conditioned on the cup/cap discipline (`AtomHasCupOrCapArity` / `CellHasCupCapGenerators` —
the whole walking-adjunction signature); the box arm's fresh block `(range n).map (· + nextFresh)` would
need the `listMapCongr` route and is not needed at the seed.  Only the wire view is covered — the `links` /
`loops` correspondence of the sigma witness is carried separately by the component machinery
(`componentComm` via the join kit, `loopsEq` via the exchange argument).

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Tier0

/-! ## The fresh shift -/

/-- Shift every identifier at or above `threshold` up by `delta`; fix every identifier below it.  The
renaming that relates a fold run at counter `threshold` to the same fold run at counter
`threshold + delta`. -/
def freshShiftAbove (threshold delta identifier : Nat) : Nat :=
  if threshold ≤ identifier then identifier + delta else identifier

/-- `freshShiftAbove` moves an at-or-above-threshold identifier up by exactly `delta`. -/
theorem freshShiftAbove_ofLe (threshold delta identifier : Nat)
    (isAtOrAboveThreshold : threshold ≤ identifier) :
    freshShiftAbove threshold delta identifier = identifier + delta :=
  if_pos isAtOrAboveThreshold

/-- `freshShiftAbove` fixes a below-threshold identifier. -/
theorem freshShiftAbove_ofNotLe (threshold delta identifier : Nat)
    (isBelowThreshold : ¬ threshold ≤ identifier) :
    freshShiftAbove threshold delta identifier = identifier :=
  if_neg isBelowThreshold

/-! ## The per-atom equivariance (cup/cap arity discipline) -/

/-- ★ **One cup/cap atom is equivariant under the fresh shift.**  If the shifted state's wires are the
shift-image of the base state's wires and its counter runs exactly `delta` ahead (with the shift threshold
at or below the base counter), the same holds after the atom: a cup splices `[nfT, nfT+1] =
[shift nfS, shift (nfS+1)]` (the splice commutes with the map, the two fresh legs are at-or-above the
threshold), a cap removes the same window pair on both sides (the removal commutes with the map, the
counter is untouched). -/
theorem stepAtom_wireView_freshShift {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (threshold delta : Nat) (stateS stateT : WireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (wiresMap : stateT.openWires = stateS.openWires.map (freshShiftAbove threshold delta))
    (freshShifted : stateT.nextFresh = stateS.nextFresh + delta)
    (thresholdLe : threshold ≤ stateS.nextFresh) :
    (stepAtom stateT atom).openWires
        = (stepAtom stateS atom).openWires.map (freshShiftAbove threshold delta)
      ∧ (stepAtom stateT atom).nextFresh = (stepAtom stateS atom).nextFresh + delta := by
  cases arity with
  | inl cupArity =>
      rw [stepAtom_ofCupArity stateT atom cupArity.1 cupArity.2,
        stepAtom_ofCupArity stateS atom cupArity.1 cupArity.2]
      constructor
      · rw [stepCup_openWires, stepCup_openWires,
          natListInsertAt_map (freshShiftAbove threshold delta) stateS.openWires
            atom.leftContext.length [stateS.nextFresh, stateS.nextFresh + 1],
          wiresMap, freshShifted]
        show natListInsertAt (stateS.openWires.map (freshShiftAbove threshold delta))
              atom.leftContext.length
              [stateS.nextFresh + delta, stateS.nextFresh + delta + 1]
            = natListInsertAt (stateS.openWires.map (freshShiftAbove threshold delta))
              atom.leftContext.length
              [freshShiftAbove threshold delta stateS.nextFresh,
                freshShiftAbove threshold delta (stateS.nextFresh + 1)]
        rw [freshShiftAbove_ofLe threshold delta stateS.nextFresh thresholdLe,
          freshShiftAbove_ofLe threshold delta (stateS.nextFresh + 1)
            (Nat.le_succ_of_le thresholdLe),
          Nat.add_right_comm stateS.nextFresh 1 delta]
      · rw [stepCup_nextFresh, stepCup_nextFresh, freshShifted,
          Nat.add_right_comm stateS.nextFresh delta 2]
  | inr capArity =>
      rw [stepAtom_ofCapArity stateT atom capArity.1 capArity.2,
        stepAtom_ofCapArity stateS atom capArity.1 capArity.2]
      constructor
      · rw [stepCap_openWires, stepCap_openWires, wiresMap,
          natListRemoveTwoAt_map (freshShiftAbove threshold delta) stateS.openWires
            atom.leftContext.length]
      · rw [stepCap_nextFresh, stepCap_nextFresh, freshShifted]

/-! ## The block layer: equivariance of a whole cell's fold -/

/-- ★ **A whole block's fold is equivariant under the fresh shift.**  Under the cup/cap generator
discipline, running the SAME cell from a shift-related state pair yields a shift-related pair: structural
cell induction mirroring `runMatchingCell_openWiresSuffix_invariant` — a generator is the atom lemma, an
identity is untouched, a vertical composite chains the two factor equivariances through
`runMatchingCell_vcomp` (the threshold bound transported along `runMatchingCell_nextFresh_le`), and the two
whiskerings only re-anchor the accumulators. -/
theorem runMatchingCell_wireView_freshShift {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (threshold delta : Nat) :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (stateS stateT : WireState) →
    CellHasCupCapGenerators cell →
    stateT.openWires = stateS.openWires.map (freshShiftAbove threshold delta) →
    stateT.nextFresh = stateS.nextFresh + delta →
    threshold ≤ stateS.nextFresh →
    (runMatchingCell stateT leftAcc rightAcc cell).openWires
        = (runMatchingCell stateS leftAcc rightAcc cell).openWires.map
            (freshShiftAbove threshold delta)
      ∧ (runMatchingCell stateT leftAcc rightAcc cell).nextFresh
          = (runMatchingCell stateS leftAcc rightAcc cell).nextFresh + delta
  | _, _, leftAcc, rightAcc, _, _, .gen generator, stateS, stateT, cupCap, wiresMap,
      freshShifted, thresholdLe =>
      stepAtom_wireView_freshShift threshold delta stateS stateT
        ⟨_, _, leftAcc, _, _, generator, rightAcc⟩ cupCap wiresMap freshShifted thresholdLe
  | _, _, _, _, _, _, .id _, _, _, _, wiresMap, freshShifted, _ =>
      ⟨wiresMap, freshShifted⟩
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellAlpha cellBeta, stateS, stateT, cupCap,
      wiresMap, freshShifted, thresholdLe => by
      have alphaShift := runMatchingCell_wireView_freshShift threshold delta leftAcc rightAcc
        cellAlpha stateS stateT cupCap.1 wiresMap freshShifted thresholdLe
      have betaShift := runMatchingCell_wireView_freshShift threshold delta leftAcc rightAcc
        cellBeta (runMatchingCell stateS leftAcc rightAcc cellAlpha)
        (runMatchingCell stateT leftAcc rightAcc cellAlpha) cupCap.2 alphaShift.1 alphaShift.2
        (Nat.le_trans thresholdLe
          (runMatchingCell_nextFresh_le stateS leftAcc rightAcc cellAlpha))
      rw [runMatchingCell_vcomp stateT leftAcc rightAcc cellAlpha cellBeta,
        runMatchingCell_vcomp stateS leftAcc rightAcc cellAlpha cellBeta]
      exact betaShift
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, stateS, stateT, cupCap,
      wiresMap, freshShifted, thresholdLe =>
      runMatchingCell_wireView_freshShift threshold delta (composePath leftAcc oneCell)
        rightAcc body stateS stateT cupCap wiresMap freshShifted thresholdLe
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, stateS, stateT, cupCap,
      wiresMap, freshShifted, thresholdLe =>
      runMatchingCell_wireView_freshShift threshold delta leftAcc
        (composePath oneCell rightAcc) body stateS stateT cupCap wiresMap freshShifted
        thresholdLe

/-! ## Honesty marker -/

/-- **Honesty marker — the fresh-shift equivariance of the WIRE VIEW is PROVED.**  Under the cup/cap
discipline, the same cell run from a `freshShiftAbove`-related state pair (wires the shift-image, counter
`delta` ahead, threshold at or below the base counter) stays shift-related in `openWires` and `nextFresh`
(`stepAtom_wireView_freshShift`, `runMatchingCell_wireView_freshShift`).  This is the fresh-id half of the
`blockRotate` witness's `openMap`: the two transposed Godement run orders run the SAME two blocks at
counters offset by the OTHER block's fresh count, so their wire lists differ exactly by the per-block
shifts the rotation composes.  NOT covered here: the `links` / `loops` correspondence (the witness reads
those through `componentComm` / `loopsEq`, via the component-algebra kit), and the box arm (excluded by the
discipline; its fresh block would need the `listMapCongr` route).  `= true`. -/
def fxMode_hasMatchingFreshShiftEquivariance : Bool := true

end FX1Poly.Tier0
