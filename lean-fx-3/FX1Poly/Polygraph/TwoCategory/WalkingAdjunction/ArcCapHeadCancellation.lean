import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadStructure

/-! # ArcCapHeadCancellation — the cap-head transport is injective

Head cancellation at the cap (peel campaign H, rung E-4).  The assembled cap-head
transport (part 11) rewrites both composite extracts over the SAME peeled cap into
transported fresh extracts; this file recovers the fresh-extract equality from the
composite-extract equality — the direction the head-cancellation assembly needs when the
two spines share the peeled head.  Every transported field is inverted: the totals by
successor injectivity, the spliced internal-count lists by insert-at cancellation (the
window position fits under both list lengths), and the partner leg by insert-at
cancellation followed by injectivity of the two-zone fresh shift.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count :=
  rangeLoopLength count []

/-- A shared front block cancels on the left of an append (structural on the block). -/
private theorem listAppendLeftCancel : (block firstList secondList : List Nat) →
    block ++ firstList = block ++ secondList → firstList = secondList
  | [], _, _, appendsEqual => appendsEqual
  | blockHead :: blockRest, firstList, secondList, appendsEqual =>
      listAppendLeftCancel blockRest firstList secondList
        (List.cons.inj (show blockHead :: (blockRest ++ firstList)
            = blockHead :: (blockRest ++ secondList) from appendsEqual)).right

/-- Splicing at position zero prepends the block (both matcher columns evaluated). -/
private theorem natListInsertAtZero : (wires block : List Nat) →
    natListInsertAt wires 0 block = block ++ wires
  | [], _ => rfl
  | _ :: _, _ => rfl

/-- Splicing the same block at the same position is left-cancellable in the list argument
when the position fits under both lists' lengths (structural on the position). -/
private theorem natListInsertAtLeftCancel (block : List Nat) :
    (position : Nat) → (firstList secondList : List Nat) →
    position ≤ firstList.length → position ≤ secondList.length →
    natListInsertAt firstList position block = natListInsertAt secondList position block →
    firstList = secondList
  | 0, firstList, secondList, _, _, insertsEqual =>
      listAppendLeftCancel block firstList secondList
        ((natListInsertAtZero firstList block).symm.trans
          (insertsEqual.trans (natListInsertAtZero secondList block)))
  | position + 1, [], _, firstFits, _, _ =>
      absurd firstFits (Nat.not_succ_le_zero position)
  | position + 1, _ :: _, [], _, secondFits, _ =>
      absurd secondFits (Nat.not_succ_le_zero position)
  | position + 1, firstHead :: firstRest, secondHead :: secondRest, firstFits, secondFits,
      insertsEqual => by
      have consEqual : firstHead :: natListInsertAt firstRest position block
          = secondHead :: natListInsertAt secondRest position block := insertsEqual
      obtain ⟨headsEqual, restsSplicedEqual⟩ := List.cons.inj consEqual
      rw [headsEqual, natListInsertAtLeftCancel block position firstRest secondRest
        (Nat.le_of_succ_le_succ firstFits) (Nat.le_of_succ_le_succ secondFits)
        restsSplicedEqual]

/-- Mapping by an injective renaming is injective on lists (structural). -/
private theorem listMapInjective (sigma : Nat → Nat)
    (isInjectiveRenaming : (firstValue secondValue : Nat) →
      sigma firstValue = sigma secondValue → firstValue = secondValue) :
    (firstList secondList : List Nat) → firstList.map sigma = secondList.map sigma →
    firstList = secondList
  | [], [], _ => rfl
  | [], secondHead :: secondRest, mapsEqual =>
      absurd
        (show sigma secondHead :: secondRest.map sigma = ([] : List Nat) from
          (show ([] : List Nat) = sigma secondHead :: secondRest.map sigma from mapsEqual).symm)
        (List.cons_ne_nil (sigma secondHead) (secondRest.map sigma))
  | firstHead :: firstRest, [], mapsEqual =>
      absurd
        (show sigma firstHead :: firstRest.map sigma = ([] : List Nat) from mapsEqual)
        (List.cons_ne_nil (sigma firstHead) (firstRest.map sigma))
  | firstHead :: firstRest, secondHead :: secondRest, mapsEqual => by
      have consEqual : sigma firstHead :: firstRest.map sigma
          = sigma secondHead :: secondRest.map sigma := mapsEqual
      obtain ⟨mappedHeadsEqual, mappedRestsEqual⟩ := List.cons.inj consEqual
      rw [isInjectiveRenaming firstHead secondHead mappedHeadsEqual,
        listMapInjective sigma isInjectiveRenaming firstRest secondRest mappedRestsEqual]

/-- Cancel a shared right addend (structural on the addend; the core cancellation lemma
leaks `propext`). -/
private theorem natSharedAddendCancel : (addend : Nat) → {firstValue secondValue : Nat} →
    firstValue + addend = secondValue + addend → firstValue = secondValue
  | 0, _, _, sumsEqual => sumsEqual
  | addend + 1, _, _, sumsEqual => natSharedAddendCancel addend (Nat.succ.inj sumsEqual)

/-- The two-zone fresh shift is injective: each zone is a strictly monotone translation,
and an above-threshold image can never equal a below-threshold one. -/
private theorem freshShiftAboveInjective (threshold delta firstValue secondValue : Nat)
    (imagesEqual : freshShiftAbove threshold delta firstValue
      = freshShiftAbove threshold delta secondValue) :
    firstValue = secondValue := by
  cases Nat.decLe threshold firstValue with
  | isTrue firstAtOrAbove =>
      cases Nat.decLe threshold secondValue with
      | isTrue secondAtOrAbove =>
          rw [freshShiftAbove_ofLe threshold delta firstValue firstAtOrAbove,
            freshShiftAbove_ofLe threshold delta secondValue secondAtOrAbove] at imagesEqual
          exact natSharedAddendCancel delta imagesEqual
      | isFalse secondBelow =>
          rw [freshShiftAbove_ofLe threshold delta firstValue firstAtOrAbove,
            freshShiftAbove_ofNotLe threshold delta secondValue secondBelow] at imagesEqual
          exact absurd
            (imagesEqual ▸ Nat.le_trans firstAtOrAbove (Nat.le_add_right firstValue delta))
            secondBelow
  | isFalse firstBelow =>
      cases Nat.decLe threshold secondValue with
      | isTrue secondAtOrAbove =>
          rw [freshShiftAbove_ofNotLe threshold delta firstValue firstBelow,
            freshShiftAbove_ofLe threshold delta secondValue secondAtOrAbove] at imagesEqual
          exact absurd
            (imagesEqual.symm ▸ Nat.le_trans secondAtOrAbove (Nat.le_add_right secondValue delta))
            firstBelow
      | isFalse secondBelow =>
          rw [freshShiftAbove_ofNotLe threshold delta firstValue firstBelow,
            freshShiftAbove_ofNotLe threshold delta secondValue secondBelow] at imagesEqual
          exact imagesEqual

/-- A `DiagramType` is determined by its four fields. -/
private theorem diagramTypeFieldsDetermine {firstDiagram secondDiagram : DiagramType}
    (bottomCountsAgree : firstDiagram.bottomCount = secondDiagram.bottomCount)
    (topCountsAgree : firstDiagram.topCount = secondDiagram.topCount)
    (partnersAgree : firstDiagram.partner = secondDiagram.partner)
    (loopCountsAgree : firstDiagram.loops = secondDiagram.loops) :
    firstDiagram = secondDiagram := by
  cases firstDiagram with
  | mk firstBottom firstTop firstPartner firstLoops =>
      cases secondDiagram with
      | mk secondBottom secondTop secondPartner secondLoops =>
          cases bottomCountsAgree
          cases topCountsAgree
          cases partnersAgree
          cases loopCountsAgree
          exact rfl

/-- A `FullArcStructure` is determined by its five fields. -/
private theorem fullArcStructureFieldsDetermine
    {firstStructure secondStructure : FullArcStructure}
    (diagramsAgree : firstStructure.diagram = secondStructure.diagram)
    (cupCountsAgree : firstStructure.cupCount = secondStructure.cupCount)
    (capCountsAgree : firstStructure.capCount = secondStructure.capCount)
    (internalCupsAgree : firstStructure.internalCupCounts = secondStructure.internalCupCounts)
    (internalCapsAgree : firstStructure.internalCapCounts = secondStructure.internalCapCounts) :
    firstStructure = secondStructure := by
  cases firstStructure with
  | mk firstDiagram firstCupCount firstCapCount firstInternalCups firstInternalCaps =>
      cases secondStructure with
      | mk secondDiagram secondCupCount secondCapCount secondInternalCups secondInternalCaps =>
          cases diagramsAgree
          cases cupCountsAgree
          cases capCountsAgree
          cases internalCupsAgree
          cases internalCapsAgree
          exact rfl

/-! ## Extract-field lengths (generic over the folded state) -/

/-- The extracted partner list ranges over all boundary ports. -/
private theorem extractArcPartnerLength (bottomCount : Nat) (state : ArcWireState) :
    (extractArc bottomCount state).diagram.partner.length
      = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length))).length
    = bottomCount + state.openWires.length
  rw [mapLength, rangeLength]

/-- The extracted internal cup-count list ranges over all boundary ports. -/
private theorem extractArcInternalCupsLength (bottomCount : Nat) (state : ArcWireState) :
    (extractArc bottomCount state).internalCupCounts.length
      = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (internalEventCountAt state.links (List.range bottomCount ++ state.openWires)
        state.cupEventNodes)).length
    = bottomCount + state.openWires.length
  rw [mapLength, rangeLength]

/-- The extracted internal cap-count list ranges over all boundary ports. -/
private theorem extractArcInternalCapsLength (bottomCount : Nat) (state : ArcWireState) :
    (extractArc bottomCount state).internalCapCounts.length
      = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (internalEventCountAt state.links (List.range bottomCount ++ state.openWires)
        state.capEventNodes)).length
    = bottomCount + state.openWires.length
  rw [mapLength, rangeLength]

/-! ## The head cancellation -/

/-- ★ **Cap-head transport cancellation**: two chained tails with the SAME composite
extract over the SAME peeled cap (window `windowPosition` at bottom boundary
`bottomCount`) already have the same fresh extract at the tail boundary.  Rewrites both
sides through the assembled transport (part 11), then inverts every transported field:
the totals by successor injectivity, the spliced internal-count lists by insert-at
cancellation, and the partner leg by insert-at cancellation followed by injectivity of
the two-zone fresh shift. -/
theorem arcCapHeadFolded_extractArc_cancel
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstChained : SpineBoundaryChained tailBoundary firstAtoms)
    (secondChained : SpineBoundaryChained tailBoundary secondAtoms)
    (compositeExtractsAgree :
      extractArc bottomCount
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) firstAtoms)
        = extractArc bottomCount
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) secondAtoms)) :
    extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) firstAtoms)
      = extractArc tailBoundary
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            secondAtoms) := by
  rw [arcCapHeadFolded_extractArc bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits firstAtoms firstChained,
    arcCapHeadFolded_extractArc bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits secondAtoms secondChained] at compositeExtractsAgree
  have windowLeTail : windowPosition ≤ tailBoundary :=
    Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
      (tailBoundaryFits.symm ▸ windowFits : windowPosition + 2 ≤ tailBoundary + 2))
  have firstPartnerImageFits : windowPosition ≤
      ((extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).diagram.partner.map (freshShiftAbove windowPosition 2)).length := by
    rw [mapLength, extractArcPartnerLength]
    exact Nat.le_trans windowLeTail
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms).openWires.length)
  have secondPartnerImageFits : windowPosition ≤
      ((extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          secondAtoms)).diagram.partner.map (freshShiftAbove windowPosition 2)).length := by
    rw [mapLength, extractArcPartnerLength]
    exact Nat.le_trans windowLeTail
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          secondAtoms).openWires.length)
  have firstInternalCupsFit : windowPosition ≤
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).internalCupCounts.length := by
    rw [extractArcInternalCupsLength]
    exact Nat.le_trans windowLeTail
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms).openWires.length)
  have secondInternalCupsFit : windowPosition ≤
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          secondAtoms)).internalCupCounts.length := by
    rw [extractArcInternalCupsLength]
    exact Nat.le_trans windowLeTail
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          secondAtoms).openWires.length)
  have firstInternalCapsFit : windowPosition ≤
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).internalCapCounts.length := by
    rw [extractArcInternalCapsLength]
    exact Nat.le_trans windowLeTail
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms).openWires.length)
  have secondInternalCapsFit : windowPosition ≤
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          secondAtoms)).internalCapCounts.length := by
    rw [extractArcInternalCapsLength]
    exact Nat.le_trans windowLeTail
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          secondAtoms).openWires.length)
  have bottomCountsAgree :
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).diagram.bottomCount
        = (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              secondAtoms)).diagram.bottomCount := rfl
  have topCountsAgree :
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).diagram.topCount
        = (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              secondAtoms)).diagram.topCount :=
    congrArg (fun transported => transported.diagram.topCount) compositeExtractsAgree
  have loopCountsAgree :
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).diagram.loops
        = (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              secondAtoms)).diagram.loops :=
    congrArg (fun transported => transported.diagram.loops) compositeExtractsAgree
  have partnersSplicedAgree :
      natListInsertAt
          ((extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              firstAtoms)).diagram.partner.map (freshShiftAbove windowPosition 2))
          windowPosition [windowPosition + 1, windowPosition]
        = natListInsertAt
            ((extractArc tailBoundary
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                secondAtoms)).diagram.partner.map (freshShiftAbove windowPosition 2))
            windowPosition [windowPosition + 1, windowPosition] :=
    congrArg (fun transported => transported.diagram.partner) compositeExtractsAgree
  have cupCountsAgree :
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).cupCount
        = (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              secondAtoms)).cupCount :=
    congrArg (fun transported => transported.cupCount) compositeExtractsAgree
  have capCountSuccessorsAgree :
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).capCount + 1
        = (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              secondAtoms)).capCount + 1 :=
    congrArg (fun transported => transported.capCount) compositeExtractsAgree
  have internalCupsSplicedAgree :
      natListInsertAt
          (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              firstAtoms)).internalCupCounts
          windowPosition [0, 0]
        = natListInsertAt
            (extractArc tailBoundary
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                secondAtoms)).internalCupCounts
            windowPosition [0, 0] :=
    congrArg (fun transported => transported.internalCupCounts) compositeExtractsAgree
  have internalCapsSplicedAgree :
      natListInsertAt
          (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              firstAtoms)).internalCapCounts
          windowPosition [1, 1]
        = natListInsertAt
            (extractArc tailBoundary
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                secondAtoms)).internalCapCounts
            windowPosition [1, 1] :=
    congrArg (fun transported => transported.internalCapCounts) compositeExtractsAgree
  have partnerImagesAgree :
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).diagram.partner.map (freshShiftAbove windowPosition 2)
        = (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              secondAtoms)).diagram.partner.map (freshShiftAbove windowPosition 2) :=
    natListInsertAtLeftCancel [windowPosition + 1, windowPosition] windowPosition
      ((extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).diagram.partner.map (freshShiftAbove windowPosition 2))
      ((extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          secondAtoms)).diagram.partner.map (freshShiftAbove windowPosition 2))
      firstPartnerImageFits secondPartnerImageFits partnersSplicedAgree
  have partnersAgree :
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).diagram.partner
        = (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              secondAtoms)).diagram.partner :=
    listMapInjective (freshShiftAbove windowPosition 2)
      (freshShiftAboveInjective windowPosition 2)
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).diagram.partner
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          secondAtoms)).diagram.partner
      partnerImagesAgree
  have internalCupsAgree :
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).internalCupCounts
        = (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              secondAtoms)).internalCupCounts :=
    natListInsertAtLeftCancel [0, 0] windowPosition
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).internalCupCounts
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          secondAtoms)).internalCupCounts
      firstInternalCupsFit secondInternalCupsFit internalCupsSplicedAgree
  have internalCapsAgree :
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).internalCapCounts
        = (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              secondAtoms)).internalCapCounts :=
    natListInsertAtLeftCancel [1, 1] windowPosition
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          firstAtoms)).internalCapCounts
      (extractArc tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          secondAtoms)).internalCapCounts
      firstInternalCapsFit secondInternalCapsFit internalCapsSplicedAgree
  exact fullArcStructureFieldsDetermine
    (diagramTypeFieldsDetermine bottomCountsAgree topCountsAgree partnersAgree loopCountsAgree)
    cupCountsAgree
    (Nat.succ.inj capCountSuccessorsAgree)
    internalCupsAgree
    internalCapsAgree

/-! ## Honesty marker -/

/-- **Honesty marker — cap-head transport cancellation (peel campaign H, rung E-4).**
`arcCapHeadFolded_extractArc_cancel`: two chained tails with the same composite extract
over the same peeled cap have the same fresh extract at the tail boundary — the assembled
transport (part 11) is injective, inverted field by field (successor injectivity on the
cap total, insert-at cancellation on the spliced lists, the injective two-zone shift on
the partner leg).  What this marker does NOT claim: the cup-head twin, locating the
matching head inside the second spine, or the head-cancellation assembly discharging
`SpineArcHeadExtractionChained` — the remaining rungs.  `= true`. -/
def fxMode_hasArcCapHeadCancellation : Bool := true

end FX1Poly.Polygraph
