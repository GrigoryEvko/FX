import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapWindowSeedReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadTransport
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadCancellation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapPeel
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapGeneration

/-! # ArcCapHeadDischarge — the chained head extraction discharges at a CAP head

The peel campaign's cap-side capstone: for a cap-arity head, the whole
`SpineArcHeadExtractionChained` conclusion assembles from the shipped chain —

  1. arc-structure equality against the cap-headed reference LOCATES the consuming cap in
     the second spine (`arcPairCapWindow_ofCapHeadExtractEq`);
  2. the located cap BUBBLES to the front with its window and boundary pinned at the seed
     (`bubblesToFront_ofArcPairCapWindow`);
  3. seed rigidity IDENTIFIES the moved atom with the head — equal boundary lengths, equal
     windows, equal arities (`adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths`);
  4. the witnessed bubble REALIZES the trace equivalence
     (`atomicTraceEquiv_of_bubblesToFront` + the spine/atomic closure identification) and
     keeps the remainder chained at the head's target boundary;
  5. the trace equivalence preserves the arc extract (`extractArc_eq_of_atomicTraceEquiv`),
     so both cap-headed folds agree, and the head CANCELS
     (`arcCapHeadFolded_extractArc_cancel`) — the tails are arc-equal at the target boundary.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range length plumbing (private copy — the seed files' kits are file-private) -/

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

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## The cap-head discharge -/

/-- ★ **The chained head extraction discharges at a CAP head.**  Both spines chained at the
running boundary with equal arc structures, the head a `2 ⇒ 0` cap: the head extracts from
the second spine by a realized trace-equivalence bubble, the remainder is chained at the
head's target boundary, and the tails are arc-equal there — the full
`SpineArcHeadExtractionChained` conclusion, cap case. -/
theorem spineArcHeadExtractionChained_ofCapArity
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCapDomArity : headAtom.generatorDom.length = 2)
    (hasCapCodArity : headAtom.generatorCod.length = 0)
    (tailList secondList : List (SpineAtom adjunctionModeSignature overallSource
      overallTarget))
    (firstChained : SpineBoundaryChained bottomCount (headAtom :: tailList))
    (secondChained : SpineBoundaryChained bottomCount secondList)
    (arcEqual : arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList) :
    ∃ matchedRemainder,
      SpineTraceEquiv adjunctionModeSignature secondList (headAtom :: matchedRemainder)
        ∧ SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder
        ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
            = arcStructureOfSpineList headAtom.codBoundaryLength matchedRemainder := by
  obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail firstChained
  have windowFits : headAtom.leftContext.length + 2 ≤ bottomCount := by
    rw [← headFires]
    show headAtom.leftContext.length + 2
      ≤ headAtom.leftContext.length + headAtom.generatorDom.length
        + headAtom.rightContext.length
    rw [hasCapDomArity]
    exact Nat.le_add_right (headAtom.leftContext.length + 2)
      headAtom.rightContext.length
  have tailBoundaryFits : headAtom.codBoundaryLength + 2 = bottomCount := by
    rw [← headFires]
    show headAtom.leftContext.length + headAtom.generatorCod.length
        + headAtom.rightContext.length + 2
      = headAtom.leftContext.length + headAtom.generatorDom.length
        + headAtom.rightContext.length
    rw [hasCapCodArity, hasCapDomArity]
    exact Nat.add_right_comm headAtom.leftContext.length headAtom.rightContext.length 2
  have extractEq : extractArc bottomCount
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          headAtom.leftContext.length) tailList)
      = extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            secondList) := by
    rw [← stepArcAtom_eq_stepCapArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) headAtom
      hasCapDomArity hasCapCodArity]
    exact arcEqual
  have located : ArcPairCapWindow bottomCount headAtom.leftContext.length
      (headAtom.leftContext.length + 1) secondList :=
    arcPairCapWindow_ofCapHeadExtractEq bottomCount headAtom.leftContext.length
      headAtom.codBoundaryLength windowFits tailBoundaryFits tailList tailChained
      secondList extractEq
  obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, movedTarget, movedPrefixAtoms,
    doesSplitSpine, witness, movedDomPin, movedCodPin, windowPin, boundaryPin⟩ :=
    bubblesToFront_ofArcPairCapWindow bottomCount headAtom.leftContext.length secondList
      windowFits secondChained located
  have movedIsHead : movedTarget = headAtom :=
    adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths movedTarget headAtom
      (boundaryPin.trans headFires.symm) windowPin
      (movedDomPin.trans hasCapDomArity.symm) (movedCodPin.trans hasCapCodArity.symm)
  have atomicEquiv : AtomicTraceEquiv adjunctionModeSignature secondList
      (headAtom :: (movedPrefixAtoms ++ suffixAtoms)) := by
    rw [doesSplitSpine, ← movedIsHead]
    exact atomicTraceEquiv_of_bubblesToFront witness suffixAtoms
  have bubbledChained : SpineBoundaryChained bottomCount
      (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) := by
    refine spineBoundaryChained_of_bubblesToFront witness suffixAtoms ?_
    rw [← doesSplitSpine]
    exact secondChained
  have remainderChained : SpineBoundaryChained headAtom.codBoundaryLength
      (movedPrefixAtoms ++ suffixAtoms) := by
    have rawRemainderChained := (spineBoundaryChained_tail bubbledChained).2
    rw [movedIsHead] at rawRemainderChained
    exact rawRemainderChained
  have hasPositiveWidth : 0 < bottomCount :=
    Nat.lt_of_lt_of_le (Nat.zero_lt_succ (headAtom.leftContext.length + 1)) windowFits
  have seedLengthEq :
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []).openWires.length
        = bottomCount := rangeLength bottomCount
  have traceInvariance : extractArc bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        secondList)
      = extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            (headAtom :: (movedPrefixAtoms ++ suffixAtoms))) :=
    extractArc_eq_of_atomicTraceEquiv atomicEquiv
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount
      bottomCount (arcStateFresh_initial bottomCount)
      (isUnionFindForest_initialLinks bottomCount) hasPositiveWidth
      (Nat.le_refl bottomCount) seedLengthEq secondChained
  have wholeAgree : extractArc bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        (headAtom :: tailList))
      = extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            (headAtom :: (movedPrefixAtoms ++ suffixAtoms))) :=
    arcEqual.trans traceInvariance
  have compositeAgree : extractArc bottomCount
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          headAtom.leftContext.length) tailList)
      = extractArc bottomCount
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              headAtom.leftContext.length) (movedPrefixAtoms ++ suffixAtoms)) := by
    rw [← stepArcAtom_eq_stepCapArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) headAtom
      hasCapDomArity hasCapCodArity]
    exact wholeAgree
  exact ⟨movedPrefixAtoms ++ suffixAtoms, atomicEquiv.toSpineTraceEquiv, remainderChained,
    arcCapHeadFolded_extractArc_cancel bottomCount headAtom.leftContext.length
      headAtom.codBoundaryLength windowFits tailBoundaryFits tailList
      (movedPrefixAtoms ++ suffixAtoms) tailChained remainderChained compositeAgree⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the CAP-head discharge is SHIPPED.**  For a cap-arity head, the
chained per-head extraction obligation's full conclusion assembles from the shipped chain:
locate (arc-structure transport), bubble (prefix descent at the seed), identify (seed
rigidity), realize (the bubble as a trace equivalence, remainder chained), cancel (the two
cap-headed folds agree, so the tails are arc-equal at the target boundary).  NOT yet
shipped: the CUP-head discharge (the orbit-form campaign) and the arity dispatch closing
`SpineArcHeadExtractionChained` itself.  `= true`. -/
def fxMode_hasArcCapHeadDischarge : Bool := true

end FX1Poly.Polygraph
