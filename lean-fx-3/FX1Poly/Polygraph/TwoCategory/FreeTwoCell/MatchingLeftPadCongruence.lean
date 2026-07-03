import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerReconstruction

/-! # MatchingLeftPadCongruence — equal base extracts give equal LEFT-padded extracts

The payoff of the left-pad simulation, mirroring `MatchingRightPadCongruence` with the pad
zone moved to the FRONT of the boundary: the padded bottom ports split as the pad ids
`[0, delta)` followed by the `delta`-offset images of the base bottom ports, and the padded
top wires split as the pad prefix followed by the shift-imaged base wires.

* `LeftPadPairedRead` — every in-range padded boundary index reads, in BOTH runs, as either
  the shift-image of the SAME base boundary read or the SAME pad-zone identifier;
* `leftPadSim_pairedReadTaxonomy` — the four-zone classification (pad bottom, shifted
  bottom, pad top, shifted top) producing the shared witness; the shifted-bottom zone
  reconciles the padded read `delta + j` with the shift image `j + delta` by commutativity;
* `matchingSameComponent_ofLeftPadSimPair` — the padded connectivity views agree: shifted
  pairs defer through `componentComm` to the base view (recovered from the base extract
  equality by `matchingConnectivityViewSim_ofExtractEq`), mixed pairs are `false` on both
  sides, pad pairs are shared identifier equality;
* `extractDiagram_ofLeftPadSimPair` — the padded extract congruence via
  `extractDiagram_eq_of_connectivityView`.

Together with the left seed instance and the two-list fold this reduces the
`whiskerLeftCongruent` field to the spine-level assembly — the next MODE3-C brick. -/

namespace FX1Poly.Polygraph

/-! ## The paired read -/

/-- A left-padded boundary index reads, in both pad-simulated runs, as either the shift-image
of the SAME base boundary read (`ofBase`) or the SAME pad-zone identifier below `delta`
(`ofPad`). -/
inductive LeftPadPairedRead (delta bottomCount : Nat)
    (stateSOne stateTOne stateSTwo stateTTwo : WireState) (index : Nat) : Prop where
  | ofBase (baseIndex : Nat)
      (baseInRange : baseIndex < bottomCount + stateSOne.openWires.length)
      (firstReadEq : natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne) index
        = freshShiftAbove 0 delta
            (natListGetAt (matchingBoundaryNodes bottomCount stateSOne) baseIndex))
      (secondReadEq : natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo) index
        = freshShiftAbove 0 delta
            (natListGetAt (matchingBoundaryNodes bottomCount stateSTwo) baseIndex))
  | ofPad (padValue : Nat) (padBelow : padValue < delta)
      (firstReadEq : natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne) index
        = padValue)
      (secondReadEq : natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo) index
        = padValue)

/-- ★ **The four-zone paired read taxonomy, left-pad edition.**  Below `delta` both runs read
the index itself (a pad identifier); inside `[delta, delta + bottomCount)` both read the
index, which IS the shift-image of the base bottom port `index - delta` (one
`Nat.add_comm`); past the bottom block the top wires read as the SAME pad identifier inside
the pad prefix and as the shift of the SAME base top read past it. -/
theorem leftPadSim_pairedReadTaxonomy (delta bottomCount : Nat)
    (stateSOne stateTOne stateSTwo stateTTwo : WireState)
    (simOne : MatchingLeftPadSim delta (padIdentifiers 0 delta) stateSOne stateTOne)
    (simTwo : MatchingLeftPadSim delta (padIdentifiers 0 delta) stateSTwo stateTTwo)
    (baseLengthsEq : stateSOne.openWires.length = stateSTwo.openWires.length)
    (index : Nat)
    (indexInRange : index < (delta + bottomCount) + stateTOne.openWires.length) :
    LeftPadPairedRead delta bottomCount stateSOne stateTOne stateSTwo stateTTwo index := by
  cases Nat.lt_or_ge index delta with
  | inl belowPad =>
      apply LeftPadPairedRead.ofPad index belowPad
      · exact matchingBoundaryNodes_getAt_bottom (delta + bottomCount) stateTOne index
          (Nat.lt_of_lt_of_le belowPad (Nat.le_add_right delta bottomCount))
      · exact matchingBoundaryNodes_getAt_bottom (delta + bottomCount) stateTTwo index
          (Nat.lt_of_lt_of_le belowPad (Nat.le_add_right delta bottomCount))
  | inr atOrPastPad =>
      cases Nat.lt_or_ge index (delta + bottomCount) with
      | inl belowBottomEnd =>
          cases Nat.le.dest atOrPastPad with
          | intro shiftedBottom shiftedBottomEq =>
              have sumBound : delta + shiftedBottom < delta + bottomCount := by
                rw [shiftedBottomEq]
                exact belowBottomEnd
              have shiftedBottomLt : shiftedBottom < bottomCount :=
                Nat.lt_of_add_lt_add_left sumBound
              apply LeftPadPairedRead.ofBase shiftedBottom
                (Nat.lt_of_lt_of_le shiftedBottomLt
                  (Nat.le_add_right bottomCount stateSOne.openWires.length))
              · rw [matchingBoundaryNodes_getAt_bottom (delta + bottomCount) stateTOne index
                    belowBottomEnd,
                  matchingBoundaryNodes_getAt_bottom bottomCount stateSOne shiftedBottom
                    shiftedBottomLt,
                  freshShiftAbove_ofLe 0 delta shiftedBottom (Nat.zero_le shiftedBottom),
                  ← shiftedBottomEq]
                exact Nat.add_comm delta shiftedBottom
              · rw [matchingBoundaryNodes_getAt_bottom (delta + bottomCount) stateTTwo index
                    belowBottomEnd,
                  matchingBoundaryNodes_getAt_bottom bottomCount stateSTwo shiftedBottom
                    shiftedBottomLt,
                  freshShiftAbove_ofLe 0 delta shiftedBottom (Nat.zero_le shiftedBottom),
                  ← shiftedBottomEq]
                exact Nat.add_comm delta shiftedBottom
      | inr atOrPastBottomEnd =>
          cases Nat.le.dest atOrPastBottomEnd with
          | intro wireOffset wireOffsetEq =>
              have wireOffsetBound : wireOffset < delta + stateSOne.openWires.length := by
                have expanded : index
                    < (delta + bottomCount) + (delta + stateSOne.openWires.length) := by
                  rw [← leftPadSim_wireCount delta (padIdentifiers 0 delta) stateSOne
                    stateTOne simOne]
                  exact indexInRange
                rw [← wireOffsetEq] at expanded
                exact Nat.lt_of_add_lt_add_left expanded
              cases Nat.lt_or_ge wireOffset delta with
              | inl wireInPad =>
                  apply LeftPadPairedRead.ofPad wireOffset wireInPad
                  · rw [← wireOffsetEq,
                      matchingBoundaryNodes_getAt_top (delta + bottomCount) stateTOne
                        wireOffset,
                      leftPadSim_wireRead_inPad delta stateSOne stateTOne simOne wireOffset
                        wireInPad]
                  · rw [← wireOffsetEq,
                      matchingBoundaryNodes_getAt_top (delta + bottomCount) stateTTwo
                        wireOffset,
                      leftPadSim_wireRead_inPad delta stateSTwo stateTTwo simTwo wireOffset
                        wireInPad]
              | inr wirePastPad =>
                  cases Nat.le.dest wirePastPad with
                  | intro baseOffset baseOffsetEq =>
                      have baseOffsetLt : baseOffset < stateSOne.openWires.length := by
                        rw [← baseOffsetEq] at wireOffsetBound
                        exact Nat.lt_of_add_lt_add_left wireOffsetBound
                      apply LeftPadPairedRead.ofBase (bottomCount + baseOffset)
                        (Nat.add_lt_add_left baseOffsetLt bottomCount)
                      · rw [← wireOffsetEq, ← baseOffsetEq,
                          matchingBoundaryNodes_getAt_top (delta + bottomCount) stateTOne
                            (delta + baseOffset),
                          leftPadSim_wireRead_inBase delta stateSOne stateTOne simOne
                            baseOffset baseOffsetLt,
                          matchingBoundaryNodes_getAt_top bottomCount stateSOne baseOffset]
                      · rw [← wireOffsetEq, ← baseOffsetEq,
                          matchingBoundaryNodes_getAt_top (delta + bottomCount) stateTTwo
                            (delta + baseOffset),
                          leftPadSim_wireRead_inBase delta stateSTwo stateTTwo simTwo
                            baseOffset (baseLengthsEq ▸ baseOffsetLt),
                          matchingBoundaryNodes_getAt_top bottomCount stateSTwo baseOffset]

/-! ## The padded connectivity views agree -/

/-- ★ **The left-padded same-component relations of two pad-simulated runs agree** given the
base connectivity-view simulation: shifted pairs defer through `componentComm` to the base
view, mixed pad/shifted pairs are `false` on both sides, and pad pairs are the SHARED
identifier equality. -/
theorem matchingSameComponent_ofLeftPadSimPair (delta bottomCount : Nat)
    (stateSOne stateTOne stateSTwo stateTTwo : WireState)
    (simOne : MatchingLeftPadSim delta (padIdentifiers 0 delta) stateSOne stateTOne)
    (simTwo : MatchingLeftPadSim delta (padIdentifiers 0 delta) stateSTwo stateTTwo)
    (baseView : MatchingConnectivityViewSim bottomCount stateSOne stateSTwo)
    (firstIndex secondIndex : Nat)
    (firstInRange : firstIndex < (delta + bottomCount) + stateTOne.openWires.length)
    (secondInRange : secondIndex < (delta + bottomCount) + stateTOne.openWires.length) :
    matchingSameComponent (delta + bottomCount) stateTOne firstIndex secondIndex
      = matchingSameComponent (delta + bottomCount) stateTTwo firstIndex secondIndex := by
  cases leftPadSim_pairedReadTaxonomy delta bottomCount stateSOne stateTOne stateSTwo
      stateTTwo simOne simTwo baseView.lengthEq firstIndex firstInRange with
  | ofBase firstBase firstBaseInRange firstReadOne firstReadTwo =>
      cases leftPadSim_pairedReadTaxonomy delta bottomCount stateSOne stateTOne stateSTwo
          stateTTwo simOne simTwo baseView.lengthEq secondIndex secondInRange with
      | ofBase secondBase secondBaseInRange secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            simOne.componentComm
              (natListGetAt (matchingBoundaryNodes bottomCount stateSOne) firstBase)
              (natListGetAt (matchingBoundaryNodes bottomCount stateSOne) secondBase),
            simTwo.componentComm
              (natListGetAt (matchingBoundaryNodes bottomCount stateSTwo) firstBase)
              (natListGetAt (matchingBoundaryNodes bottomCount stateSTwo) secondBase)]
          exact baseView.viewAgrees firstBase secondBase
            (baseView.lengthEq ▸ firstBaseInRange) (baseView.lengthEq ▸ secondBaseInRange)
      | ofPad secondPad secondPadBelow secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            leftPadSim_shiftedVsPad_isFalse delta (padIdentifiers 0 delta) stateSOne
              stateTOne simOne
              (natListGetAt (matchingBoundaryNodes bottomCount stateSOne) firstBase)
              secondPad secondPadBelow,
            leftPadSim_shiftedVsPad_isFalse delta (padIdentifiers 0 delta) stateSTwo
              stateTTwo simTwo
              (natListGetAt (matchingBoundaryNodes bottomCount stateSTwo) firstBase)
              secondPad secondPadBelow]
  | ofPad firstPad firstPadBelow firstReadOne firstReadTwo =>
      cases leftPadSim_pairedReadTaxonomy delta bottomCount stateSOne stateTOne stateSTwo
          stateTTwo simOne simTwo baseView.lengthEq secondIndex secondInRange with
      | ofBase secondBase secondBaseInRange secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            leftPadSim_padVsShifted_isFalse delta (padIdentifiers 0 delta) stateSOne
              stateTOne simOne firstPad
              (natListGetAt (matchingBoundaryNodes bottomCount stateSOne) secondBase)
              firstPadBelow,
            leftPadSim_padVsShifted_isFalse delta (padIdentifiers 0 delta) stateSTwo
              stateTTwo simTwo firstPad
              (natListGetAt (matchingBoundaryNodes bottomCount stateSTwo) secondBase)
              firstPadBelow]
      | ofPad secondPad secondPadBelow secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            leftPadSim_padVsPad delta (padIdentifiers 0 delta) stateSOne stateTOne simOne
              firstPad secondPad firstPadBelow secondPadBelow,
            leftPadSim_padVsPad delta (padIdentifiers 0 delta) stateSTwo stateTTwo simTwo
              firstPad secondPad firstPadBelow secondPadBelow]

/-! ## The payoff: the left-padded extract congruence -/

/-- ★ **Equal base extracts give equal LEFT-padded extracts** across two left-pad-simulated
runs.  The base extract equality reconstructs the base connectivity view
(`matchingConnectivityViewSim_ofExtractEq`), the paired read taxonomy transports it through
the front pad zones, and the padded connectivity view determines the padded extract. -/
theorem extractDiagram_ofLeftPadSimPair (delta bottomCount : Nat)
    (stateSOne stateTOne stateSTwo stateTTwo : WireState)
    (simOne : MatchingLeftPadSim delta (padIdentifiers 0 delta) stateSOne stateTOne)
    (simTwo : MatchingLeftPadSim delta (padIdentifiers 0 delta) stateSTwo stateTTwo)
    (baseExtractsEqual : extractDiagram bottomCount stateSOne
      = extractDiagram bottomCount stateSTwo) :
    extractDiagram (delta + bottomCount) stateTOne
      = extractDiagram (delta + bottomCount) stateTTwo := by
  have baseView := matchingConnectivityViewSim_ofExtractEq bottomCount stateSOne stateSTwo
    baseExtractsEqual
  apply extractDiagram_eq_of_connectivityView (delta + bottomCount) stateTOne stateTTwo
  · rw [leftPadSim_wireCount delta (padIdentifiers 0 delta) stateSOne stateTOne simOne,
      leftPadSim_wireCount delta (padIdentifiers 0 delta) stateSTwo stateTTwo simTwo,
      baseView.lengthEq]
  · rw [simOne.loopsEq, simTwo.loopsEq, baseView.loopsEq]
  · exact matchingSameComponent_ofLeftPadSimPair delta bottomCount stateSOne stateTOne
      stateSTwo stateTTwo simOne simTwo baseView

/-! ## Honesty marker -/

/-- **Honesty marker — the left-padded extract congruence is SHIPPED.**  Two left-pad-simulated
runs with equal base extracts extract identically at the padded boundary
(`extractDiagram_ofLeftPadSimPair`): the base view is reconstructed from the extract
(`matchingConnectivityViewSim_ofExtractEq`), the paired four-zone read taxonomy carries it
through the front pad, and the connectivity view determines the extract.  The spine-level
whiskerLeft assembly is the next MODE3-C brick.  `= true`. -/
def fxMode_hasMatchingLeftPadExtractCongruence : Bool := true

end FX1Poly.Polygraph
