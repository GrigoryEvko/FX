import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerReconstruction

/-! # MatchingRightPadCongruence — equal base extracts give equal padded extracts

The payoff of the right-pad simulation: two pad-simulated runs whose BASE states extract
identically extract identically at the PADDED boundary.

* `RightPadPairedRead` — every in-range padded boundary index reads, in BOTH runs, as either
  the shift-image of the SAME base boundary read or the SAME pad-zone identifier;
* `rightPadSim_pairedReadTaxonomy` — the four-zone classification (real bottom, pad bottom,
  shifted top, pad top) producing the shared witness;
* `matchingSameComponent_ofRightPadSimPair` — the padded connectivity views agree: shifted
  pairs defer through `componentComm` to the base view (recovered from the base extract
  equality by `matchingConnectivityViewSim_ofExtractEq`), mixed pairs are `false` on both
  sides, pad pairs are shared identifier equality;
* `extractDiagram_ofRightPadSimPair` — the padded extract congruence via
  `extractDiagram_eq_of_connectivityView`.

Together with the seed instance and the boundary-disciplined fold this reduces the
`whiskerRightCongruent` field to the spine-level assembly — the next MODE3-C brick. -/

namespace FX1Poly.Polygraph

/-! ## The paired read -/

/-- A padded boundary index reads, in both pad-simulated runs, as either the shift-image of
the SAME base boundary read (`ofBase`) or the SAME pad-zone identifier (`ofPad`). -/
inductive RightPadPairedRead (threshold delta : Nat)
    (stateSOne stateTOne stateSTwo stateTTwo : WireState) (index : Nat) : Prop where
  | ofBase (baseIndex : Nat)
      (baseInRange : baseIndex < threshold + stateSOne.openWires.length)
      (firstReadEq : natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne) index
        = freshShiftAbove threshold delta
            (natListGetAt (matchingBoundaryNodes threshold stateSOne) baseIndex))
      (secondReadEq : natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo) index
        = freshShiftAbove threshold delta
            (natListGetAt (matchingBoundaryNodes threshold stateSTwo) baseIndex))
  | ofPad (padValue : Nat)
      (padLower : threshold ≤ padValue) (padUpper : padValue < threshold + delta)
      (firstReadEq : natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne) index
        = padValue)
      (secondReadEq : natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo) index
        = padValue)

/-- ★ **The four-zone paired read taxonomy.**  Below the threshold both runs read the index
itself (a fixed shift-image); inside `[threshold, threshold + delta)` both read the index as a
pad identifier; past the pad the top wires read as the shift of the SAME base top read inside
the base image and as the SAME pad identifier past it. -/
theorem rightPadSim_pairedReadTaxonomy (threshold delta : Nat)
    (stateSOne stateTOne stateSTwo stateTTwo : WireState)
    (simOne : MatchingRightPadSim threshold delta (padIdentifiers threshold delta)
      stateSOne stateTOne)
    (simTwo : MatchingRightPadSim threshold delta (padIdentifiers threshold delta)
      stateSTwo stateTTwo)
    (baseLengthsEq : stateSOne.openWires.length = stateSTwo.openWires.length)
    (index : Nat)
    (indexInRange : index < (threshold + delta) + stateTOne.openWires.length) :
    RightPadPairedRead threshold delta stateSOne stateTOne stateSTwo stateTTwo index := by
  cases Nat.lt_or_ge index threshold with
  | inl belowThreshold =>
      apply RightPadPairedRead.ofBase index
        (Nat.lt_of_lt_of_le belowThreshold
          (Nat.le_add_right threshold stateSOne.openWires.length))
      · rw [matchingBoundaryNodes_getAt_bottom (threshold + delta) stateTOne index
            (Nat.lt_of_lt_of_le belowThreshold (Nat.le_add_right threshold delta)),
          matchingBoundaryNodes_getAt_bottom threshold stateSOne index belowThreshold,
          freshShiftAbove_fixesBelow threshold delta index belowThreshold]
      · rw [matchingBoundaryNodes_getAt_bottom (threshold + delta) stateTTwo index
            (Nat.lt_of_lt_of_le belowThreshold (Nat.le_add_right threshold delta)),
          matchingBoundaryNodes_getAt_bottom threshold stateSTwo index belowThreshold,
          freshShiftAbove_fixesBelow threshold delta index belowThreshold]
  | inr atOrAboveThreshold =>
      cases Nat.lt_or_ge index (threshold + delta) with
      | inl belowPadEnd =>
          apply RightPadPairedRead.ofPad index atOrAboveThreshold belowPadEnd
          · exact matchingBoundaryNodes_getAt_bottom (threshold + delta) stateTOne index
              belowPadEnd
          · exact matchingBoundaryNodes_getAt_bottom (threshold + delta) stateTTwo index
              belowPadEnd
      | inr atOrPastPadEnd =>
          cases Nat.le.dest atOrPastPadEnd with
          | intro offset offsetEq =>
              cases Nat.lt_or_ge offset stateSOne.openWires.length with
              | inl offsetInBase =>
                  apply RightPadPairedRead.ofBase (threshold + offset)
                    (Nat.add_lt_add_left offsetInBase threshold)
                  · rw [← offsetEq,
                      matchingBoundaryNodes_getAt_top (threshold + delta) stateTOne offset,
                      rightPadSim_wireRead_inBase threshold delta stateSOne stateTOne simOne
                        offset offsetInBase,
                      matchingBoundaryNodes_getAt_top threshold stateSOne offset]
                  · rw [← offsetEq,
                      matchingBoundaryNodes_getAt_top (threshold + delta) stateTTwo offset,
                      rightPadSim_wireRead_inBase threshold delta stateSTwo stateTTwo simTwo
                        offset (baseLengthsEq ▸ offsetInBase),
                      matchingBoundaryNodes_getAt_top threshold stateSTwo offset]
              | inr offsetAtOrPastBase =>
                  cases Nat.le.dest offsetAtOrPastBase with
                  | intro padOffset padOffsetEq =>
                      have offsetBound : offset < stateSOne.openWires.length + delta := by
                        have expanded : index
                            < threshold + delta + (stateSOne.openWires.length + delta) := by
                          rw [← rightPadSim_wireCount threshold delta stateSOne stateTOne
                            simOne]
                          exact indexInRange
                        rw [← offsetEq] at expanded
                        exact Nat.lt_of_add_lt_add_left expanded
                      have padOffsetLt : padOffset < delta := by
                        rw [← padOffsetEq] at offsetBound
                        exact Nat.lt_of_add_lt_add_left offsetBound
                      apply RightPadPairedRead.ofPad (threshold + padOffset)
                        (Nat.le_add_right threshold padOffset)
                        (Nat.add_lt_add_left padOffsetLt threshold)
                      · rw [← offsetEq, ← padOffsetEq,
                          matchingBoundaryNodes_getAt_top (threshold + delta) stateTOne
                            (stateSOne.openWires.length + padOffset),
                          rightPadSim_wireRead_inPad threshold delta stateSOne stateTOne
                            simOne padOffset padOffsetLt]
                      · rw [← offsetEq, ← padOffsetEq,
                          matchingBoundaryNodes_getAt_top (threshold + delta) stateTTwo
                            (stateSOne.openWires.length + padOffset),
                          baseLengthsEq,
                          rightPadSim_wireRead_inPad threshold delta stateSTwo stateTTwo
                            simTwo padOffset padOffsetLt]

/-! ## The padded connectivity views agree -/

/-- ★ **The padded same-component relations of two pad-simulated runs agree** given the base
connectivity-view simulation: shifted pairs defer through `componentComm` to the base view,
mixed pad/shifted pairs are `false` on both sides, and pad pairs are the SHARED identifier
equality. -/
theorem matchingSameComponent_ofRightPadSimPair (threshold delta : Nat)
    (stateSOne stateTOne stateSTwo stateTTwo : WireState)
    (simOne : MatchingRightPadSim threshold delta (padIdentifiers threshold delta)
      stateSOne stateTOne)
    (simTwo : MatchingRightPadSim threshold delta (padIdentifiers threshold delta)
      stateSTwo stateTTwo)
    (baseView : MatchingConnectivityViewSim threshold stateSOne stateSTwo)
    (firstIndex secondIndex : Nat)
    (firstInRange : firstIndex < (threshold + delta) + stateTOne.openWires.length)
    (secondInRange : secondIndex < (threshold + delta) + stateTOne.openWires.length) :
    matchingSameComponent (threshold + delta) stateTOne firstIndex secondIndex
      = matchingSameComponent (threshold + delta) stateTTwo firstIndex secondIndex := by
  cases rightPadSim_pairedReadTaxonomy threshold delta stateSOne stateTOne stateSTwo stateTTwo
      simOne simTwo baseView.lengthEq firstIndex firstInRange with
  | ofBase firstBase firstBaseInRange firstReadOne firstReadTwo =>
      cases rightPadSim_pairedReadTaxonomy threshold delta stateSOne stateTOne stateSTwo
          stateTTwo simOne simTwo baseView.lengthEq secondIndex secondInRange with
      | ofBase secondBase secondBaseInRange secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            simOne.componentComm
              (natListGetAt (matchingBoundaryNodes threshold stateSOne) firstBase)
              (natListGetAt (matchingBoundaryNodes threshold stateSOne) secondBase),
            simTwo.componentComm
              (natListGetAt (matchingBoundaryNodes threshold stateSTwo) firstBase)
              (natListGetAt (matchingBoundaryNodes threshold stateSTwo) secondBase)]
          exact baseView.viewAgrees firstBase secondBase
            (baseView.lengthEq ▸ firstBaseInRange) (baseView.lengthEq ▸ secondBaseInRange)
      | ofPad secondPad secondPadLower secondPadUpper secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            rightPadSim_shiftedVsPad_isFalse threshold delta (padIdentifiers threshold delta)
              stateSOne stateTOne simOne
              (natListGetAt (matchingBoundaryNodes threshold stateSOne) firstBase)
              secondPad secondPadLower secondPadUpper,
            rightPadSim_shiftedVsPad_isFalse threshold delta (padIdentifiers threshold delta)
              stateSTwo stateTTwo simTwo
              (natListGetAt (matchingBoundaryNodes threshold stateSTwo) firstBase)
              secondPad secondPadLower secondPadUpper]
  | ofPad firstPad firstPadLower firstPadUpper firstReadOne firstReadTwo =>
      cases rightPadSim_pairedReadTaxonomy threshold delta stateSOne stateTOne stateSTwo
          stateTTwo simOne simTwo baseView.lengthEq secondIndex secondInRange with
      | ofBase secondBase secondBaseInRange secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            rightPadSim_padVsShifted_isFalse threshold delta (padIdentifiers threshold delta)
              stateSOne stateTOne simOne firstPad
              (natListGetAt (matchingBoundaryNodes threshold stateSOne) secondBase)
              firstPadLower firstPadUpper,
            rightPadSim_padVsShifted_isFalse threshold delta (padIdentifiers threshold delta)
              stateSTwo stateTTwo simTwo firstPad
              (natListGetAt (matchingBoundaryNodes threshold stateSTwo) secondBase)
              firstPadLower firstPadUpper]
      | ofPad secondPad secondPadLower secondPadUpper secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            rightPadSim_padVsPad threshold delta (padIdentifiers threshold delta) stateSOne
              stateTOne simOne firstPad secondPad firstPadLower firstPadUpper secondPadLower
              secondPadUpper,
            rightPadSim_padVsPad threshold delta (padIdentifiers threshold delta) stateSTwo
              stateTTwo simTwo firstPad secondPad firstPadLower firstPadUpper secondPadLower
              secondPadUpper]

/-! ## The payoff: the padded extract congruence -/

/-- ★ **Equal base extracts give equal padded extracts** across two right-pad-simulated runs.
The base extract equality reconstructs the base connectivity view
(`matchingConnectivityViewSim_ofExtractEq`), the paired read taxonomy transports it through
the pad zones, and the padded connectivity view determines the padded extract. -/
theorem extractDiagram_ofRightPadSimPair (threshold delta : Nat)
    (stateSOne stateTOne stateSTwo stateTTwo : WireState)
    (simOne : MatchingRightPadSim threshold delta (padIdentifiers threshold delta)
      stateSOne stateTOne)
    (simTwo : MatchingRightPadSim threshold delta (padIdentifiers threshold delta)
      stateSTwo stateTTwo)
    (baseExtractsEqual : extractDiagram threshold stateSOne
      = extractDiagram threshold stateSTwo) :
    extractDiagram (threshold + delta) stateTOne
      = extractDiagram (threshold + delta) stateTTwo := by
  have baseView := matchingConnectivityViewSim_ofExtractEq threshold stateSOne stateSTwo
    baseExtractsEqual
  apply extractDiagram_eq_of_connectivityView (threshold + delta) stateTOne stateTTwo
  · rw [rightPadSim_wireCount threshold delta stateSOne stateTOne simOne,
      rightPadSim_wireCount threshold delta stateSTwo stateTTwo simTwo, baseView.lengthEq]
  · rw [simOne.loopsEq, simTwo.loopsEq, baseView.loopsEq]
  · exact matchingSameComponent_ofRightPadSimPair threshold delta stateSOne stateTOne
      stateSTwo stateTTwo simOne simTwo baseView

/-! ## Honesty marker -/

/-- **Honesty marker — the padded extract congruence is SHIPPED.**  Two right-pad-simulated
runs with equal base extracts extract identically at the padded boundary
(`extractDiagram_ofRightPadSimPair`): the base view is reconstructed from the extract
(`matchingConnectivityViewSim_ofExtractEq`), the paired four-zone read taxonomy carries it
through the pad, and the connectivity view determines the extract.  NOT yet shipped: the
spine-level `whiskerRightCongruent` assembly gluing this to the seed instance, the
boundary-disciplined fold, and the right-whisker action invisibility — the next MODE3-C
brick.  `= true`. -/
def fxMode_hasMatchingRightPadExtractCongruence : Bool := true

end FX1Poly.Polygraph
