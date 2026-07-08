import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingStepCupWindowPartner
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRangeInterleave

/-! # MatchingDropLastCup — dropping a top-of-stack cup is matching-injective (Track B route 1, brick 3)

Building on the plain census core (`partnerIndexOf_stepCup_old`) and the two census-free window partners
(`generalStateCupForwardPartnerMatching`, `generalStateCupBackwardPartnerMatching`), this file expresses the
boundary partner list of `extractDiagram bc (stepCup S w)` as a fixed INJECTIVE function of the base partner list
— the short chord `[bc+w+1, bc+w]` spliced over the window shift `freshShiftAbove (bc+w) 2` — and cancels a shared
last cup to prove `dropLastCup_matching_injective`.

The plain assembly is STRICTLY SMALLER than the arc original: `DiagramType` has 4 fields (bottomCount, topCount,
partner, loops) versus `FullArcStructure`'s 8, so the reassembly inverts only `topCount` (+2, right-cancel) and
`partner` (splice + shift, left-injective + map-shift-injective); `bottomCount` and `loops` are `rfl`, and all four
arc count-list fields vanish.

  * ★ `diagramPartner_stepCup` — the plain analogue of `diagramPartner_stepCupArc`: old ports keep their partner at
    the shifted position (`partnerIndexOf_stepCup_old`), and the two fresh legs partner each other (the forward and
    backward window partners), so the stepped partner list is the base list shifted with the short chord spliced.
  * ★ `dropLastCup_matching_injective` — the width-`0` linchpin: two boundary-chained pure-cup spines over the
    width-`0` bottom boundary sharing a last cup with EQUAL `matchingOfSpineList 0` have equal-matching prefixes.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / list plumbing (per-file copies, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]; exact Nat.add_zero count

private theorem appendAssoc : (front middle back : List Nat) →
    (front ++ middle) ++ back = front ++ (middle ++ back)
  | [], _, _ => rfl
  | headWire :: frontRest, middle, back =>
      congrArg (fun joined => headWire :: joined) (appendAssoc frontRest middle back)

private theorem windowSplitTotals (seedBoundary openLen windowPosition tailCount : Nat)
    (tailSpec : windowPosition + tailCount = openLen) :
    seedBoundary + (openLen + 2) = (seedBoundary + windowPosition + 2) + tailCount
      ∧ seedBoundary + openLen = (seedBoundary + windowPosition) + tailCount := by
  refine ⟨?_, ?_⟩
  · rw [← tailSpec, ← Nat.add_assoc seedBoundary (windowPosition + tailCount) 2,
      ← Nat.add_assoc seedBoundary windowPosition tailCount,
      Nat.add_right_comm (seedBoundary + windowPosition) tailCount 2]
  · rw [← tailSpec, ← Nat.add_assoc seedBoundary windowPosition tailCount]

private theorem natListInsertAt_splitsAtLength : (front : List Nat) → (position : Nat) →
    (back block : List Nat) → front.length = position →
    natListInsertAt (front ++ back) position block = front ++ (block ++ back)
  | [], position, back, block, lengthEq => by
      cases lengthEq
      cases back with
      | nil => exact rfl
      | cons headWire restWires => exact rfl
  | headWire :: frontRest, position, back, block, lengthEq => by
      cases lengthEq
      show headWire :: natListInsertAt (frontRest ++ back) frontRest.length block
        = headWire :: (frontRest ++ (block ++ back))
      exact congrArg (fun spliced => headWire :: spliced)
        (natListInsertAt_splitsAtLength frontRest frontRest.length back block rfl)

/-- A map whose every entry factors through a shifted base read IS the double map (structural — no `funext`). -/
private theorem listMapFactorsThroughShift (compositeRead freshRead indexShift : Nat → Nat) :
    (candidates : List Nat) →
    (∀ candidate, candidate ∈ candidates → compositeRead candidate = indexShift (freshRead candidate)) →
    candidates.map compositeRead = (candidates.map freshRead).map indexShift
  | [], _ => rfl
  | headCandidate :: rest, pointwise => by
      show compositeRead headCandidate :: rest.map compositeRead
        = indexShift (freshRead headCandidate) :: (rest.map freshRead).map indexShift
      rw [pointwise headCandidate (List.Mem.head rest),
        listMapFactorsThroughShift compositeRead freshRead indexShift rest
          (fun laterCandidate laterMem => pointwise laterCandidate (List.Mem.tail headCandidate laterMem))]

/-- The past-window variant: composite reads at `windowPosition + 2 + offset` factor through fresh reads at
`windowPosition + offset`. -/
private theorem listMapPastWindowFactors (compositeRead freshRead indexShift : Nat → Nat) (windowPosition : Nat) :
    (offsets : List Nat) →
    (∀ offset, offset ∈ offsets →
      compositeRead (windowPosition + 2 + offset) = indexShift (freshRead (windowPosition + offset))) →
    (offsets.map (fun offset => windowPosition + 2 + offset)).map compositeRead
      = ((offsets.map (fun offset => windowPosition + offset)).map freshRead).map indexShift
  | [], _ => rfl
  | headOffset :: rest, pointwise => by
      show compositeRead (windowPosition + 2 + headOffset)
          :: (rest.map (fun offset => windowPosition + 2 + offset)).map compositeRead
        = indexShift (freshRead (windowPosition + headOffset))
          :: ((rest.map (fun offset => windowPosition + offset)).map freshRead).map indexShift
      rw [pointwise headOffset (List.Mem.head rest),
        listMapPastWindowFactors compositeRead freshRead indexShift windowPosition rest
          (fun laterOffset laterMem => pointwise laterOffset (List.Mem.tail headOffset laterMem))]

/-! ## LEG 3 — the boundary partner list -/

/-- ★ **A top-of-stack cup splices the short chord into the boundary partner list (plain carrier).**  The composite
extract's partner list equals the base partner list transported through the window index shift
`freshShiftAbove (bc + w) 2` with the short chord `[bc + w + 1, bc + w]` spliced at the window: old ports keep their
partner at the shifted position (`partnerIndexOf_stepCup_old`), and the two fresh legs partner each other (the
forward + backward window partners).  The plain analogue of `diagramPartner_stepCupArc`, census-free. -/
theorem diagramPartner_stepCup (seedBoundary : Nat) (state : WireState) (windowPosition : Nat)
    (fresh : WireStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (windowFits : windowPosition ≤ state.openWires.length) :
    (extractDiagram seedBoundary (stepCup state windowPosition)).partner
      = natListInsertAt
          ((extractDiagram seedBoundary state).partner.map
            (freshShiftAbove (seedBoundary + windowPosition) 2))
          (seedBoundary + windowPosition)
          [seedBoundary + windowPosition + 1, seedBoundary + windowPosition] := by
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowFits
  have steppedOpenLen : (stepCup state windowPosition).openWires.length = state.openWires.length + 2 :=
    natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]
  obtain ⟨steppedTotalEq, baseTotalEq⟩ :=
    windowSplitTotals seedBoundary state.openWires.length windowPosition tailCount tailSpec
  have windowLeSum : seedBoundary + windowPosition ≤ seedBoundary + state.openWires.length :=
    Nat.add_le_add_left windowFits seedBoundary
  -- the two window entries (forward / backward window partners, census-free)
  have windowLeft : partnerIndexOf (stepCup state windowPosition).links
      (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
      (seedBoundary + (stepCup state windowPosition).openWires.length) (seedBoundary + windowPosition)
      = seedBoundary + windowPosition + 1 :=
    generalStateCupForwardPartnerMatching seedBoundary state windowPosition forest fresh seedBelowFresh windowFits
  have windowRight : partnerIndexOf (stepCup state windowPosition).links
      (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
      (seedBoundary + (stepCup state windowPosition).openWires.length) (seedBoundary + windowPosition + 1)
      = seedBoundary + windowPosition :=
    generalStateCupBackwardPartnerMatching seedBoundary state windowPosition forest fresh seedBelowFresh windowFits
  -- unfold both sides to the map forms
  show (List.range (seedBoundary + (stepCup state windowPosition).openWires.length)).map
      (partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length))
    = natListInsertAt
        (((List.range (seedBoundary + state.openWires.length)).map
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2))
        (seedBoundary + windowPosition)
        [seedBoundary + windowPosition + 1, seedBoundary + windowPosition]
  have compositeCandidatesEq : List.range (seedBoundary + (stepCup state windowPosition).openWires.length)
      = List.range ((seedBoundary + windowPosition + 2) + tailCount) := by
    rw [steppedOpenLen, steppedTotalEq]
  have freshCandidatesSplitEq : List.range (seedBoundary + state.openWires.length)
      = List.range (seedBoundary + windowPosition)
          ++ (List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset) :=
    (congrArg List.range baseTotalEq).trans (rangeSplit (seedBoundary + windowPosition) tailCount)
  have belowSegEq : (List.range (seedBoundary + windowPosition)).map
      (partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length))
      = ((List.range (seedBoundary + windowPosition)).map
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2) :=
    listMapFactorsThroughShift
      (partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length))
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))
      (freshShiftAbove (seedBoundary + windowPosition) 2) (List.range (seedBoundary + windowPosition))
      (fun candidate candidateMem => by
        have candidateBelow : candidate < seedBoundary + windowPosition := mem_range_imp_lt candidateMem
        have shiftFixed : freshShiftAbove (seedBoundary + windowPosition) 2 candidate = candidate :=
          freshShiftAbove_ofNotLe (seedBoundary + windowPosition) 2 candidate (Nat.not_le_of_gt candidateBelow)
        have corr := partnerIndexOf_stepCup_old seedBoundary state windowPosition fresh forest
          seedBelowFresh windowFits candidate (Nat.lt_of_lt_of_le candidateBelow windowLeSum)
        rw [shiftFixed] at corr
        exact corr)
  have pastSegEq : ((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + 2 + offset)).map
      (partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length))
      = (((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset)).map
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2) :=
    listMapPastWindowFactors
      (partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length))
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))
      (freshShiftAbove (seedBoundary + windowPosition) 2) (seedBoundary + windowPosition) (List.range tailCount)
      (fun offset offsetMem => by
        have offsetBelow : offset < tailCount := mem_range_imp_lt offsetMem
        have idxInRange : seedBoundary + windowPosition + offset < seedBoundary + state.openWires.length := by
          rw [baseTotalEq]; exact Nat.add_lt_add_left offsetBelow (seedBoundary + windowPosition)
        have shiftPast : freshShiftAbove (seedBoundary + windowPosition) 2 (seedBoundary + windowPosition + offset)
            = seedBoundary + windowPosition + offset + 2 :=
          freshShiftAbove_ofLe (seedBoundary + windowPosition) 2 (seedBoundary + windowPosition + offset)
            (Nat.le_add_right (seedBoundary + windowPosition) offset)
        have corr := partnerIndexOf_stepCup_old seedBoundary state windowPosition fresh forest
          seedBelowFresh windowFits (seedBoundary + windowPosition + offset) idxInRange
        rw [shiftPast, Nat.add_right_comm (seedBoundary + windowPosition) offset 2] at corr
        exact corr)
  have windowSegEq : ([seedBoundary + windowPosition, seedBoundary + windowPosition + 1]).map
      (partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length))
      = [seedBoundary + windowPosition + 1, seedBoundary + windowPosition] := by
    show partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length) (seedBoundary + windowPosition)
      :: partnerIndexOf (stepCup state windowPosition).links
          (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
          (seedBoundary + (stepCup state windowPosition).openWires.length) (seedBoundary + windowPosition + 1)
      :: [] = [seedBoundary + windowPosition + 1, seedBoundary + windowPosition]
    rw [windowLeft, windowRight]
  have frontLengthEq : (((List.range (seedBoundary + windowPosition)).map
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2)).length
      = seedBoundary + windowPosition :=
    (mapLength (freshShiftAbove (seedBoundary + windowPosition) 2)
        ((List.range (seedBoundary + windowPosition)).map
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length)))).trans
      ((mapLength
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length)) (List.range (seedBoundary + windowPosition))).trans
        (rangeLength (seedBoundary + windowPosition)))
  rw [compositeCandidatesEq, rangeInterleaveAtWindow (seedBoundary + windowPosition) tailCount,
    mapAppend
      (partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length))
      (List.range (seedBoundary + windowPosition) ++ [seedBoundary + windowPosition, seedBoundary + windowPosition + 1])
      ((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + 2 + offset)),
    mapAppend
      (partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length))
      (List.range (seedBoundary + windowPosition))
      [seedBoundary + windowPosition, seedBoundary + windowPosition + 1],
    freshCandidatesSplitEq,
    mapAppend
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))
      (List.range (seedBoundary + windowPosition))
      ((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset)),
    mapAppend (freshShiftAbove (seedBoundary + windowPosition) 2)
      ((List.range (seedBoundary + windowPosition)).map
        (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
          (seedBoundary + state.openWires.length)))
      (((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset)).map
        (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
          (seedBoundary + state.openWires.length))),
    natListInsertAt_splitsAtLength
      (((List.range (seedBoundary + windowPosition)).map
        (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
          (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2))
      (seedBoundary + windowPosition)
      ((((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset)).map
        (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
          (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2))
      [seedBoundary + windowPosition + 1, seedBoundary + windowPosition] frontLengthEq,
    belowSegEq, windowSegEq, pastSegEq]
  exact appendAssoc
    (((List.range (seedBoundary + windowPosition)).map
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2))
    [seedBoundary + windowPosition + 1, seedBoundary + windowPosition]
    ((((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset)).map
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2))

/-! ## LEG 4 — the assembly: dropping a top-of-stack cup is injective on the width-0 matching -/

/-- `Nat` right-cancellation, propext-free. -/
private theorem addRightCancel : (summand leftValue rightValue : Nat) →
    leftValue + summand = rightValue + summand → leftValue = rightValue
  | 0, _, _, h => h
  | summand + 1, leftValue, rightValue, h => addRightCancel summand leftValue rightValue (Nat.succ.inj h)

/-- `List` append is left-cancellative (structural on the shared front). -/
private theorem appendLeftCancel : (block first second : List Nat) →
    block ++ first = block ++ second → first = second
  | [], _, _, h => h
  | headWire :: rest, first, second, h => by
      have hcons : headWire :: (rest ++ first) = headWire :: (rest ++ second) := h
      injection hcons with _ tailEq
      exact appendLeftCancel rest first second tailEq

private theorem natListInsertAtZeroCancel (block first second : List Nat)
    (h : natListInsertAt first 0 block = natListInsertAt second 0 block) : first = second := by
  rw [natListInsertAt_zero, natListInsertAt_zero] at h
  exact appendLeftCancel block first second h

/-- `natListInsertAt` at a fixed in-range position with a fixed block is left-injective. -/
private theorem natListInsertAt_leftInjective : (position : Nat) → (block first second : List Nat) →
    position ≤ first.length → position ≤ second.length →
    natListInsertAt first position block = natListInsertAt second position block → first = second
  | 0, block, first, second, _, _, h => natListInsertAtZeroCancel block first second h
  | _ + 1, _, [], _, pLe, _, _ => absurd pLe (Nat.not_succ_le_zero _)
  | _ + 1, _, _ :: _, [], _, pLe, _ => absurd pLe (Nat.not_succ_le_zero _)
  | position + 1, block, headFirst :: restFirst, headSecond :: restSecond, pLeFirst, pLeSecond, h => by
      have hcons : headFirst :: natListInsertAt restFirst position block
          = headSecond :: natListInsertAt restSecond position block := h
      injection hcons with hHead hRest
      rw [hHead, natListInsertAt_leftInjective position block restFirst restSecond
        (Nat.le_of_succ_le_succ pLeFirst) (Nat.le_of_succ_le_succ pLeSecond) hRest]

/-- `freshShiftAbove threshold 2` is injective. -/
private theorem freshShiftInjective (threshold a b : Nat)
    (shiftEq : freshShiftAbove threshold 2 a = freshShiftAbove threshold 2 b) : a = b := by
  cases Nat.decLe threshold a with
  | isTrue aGe =>
      cases Nat.decLe threshold b with
      | isTrue bGe =>
          rw [freshShiftAbove_ofLe threshold 2 a aGe, freshShiftAbove_ofLe threshold 2 b bGe] at shiftEq
          exact addRightCancel 2 a b shiftEq
      | isFalse bLt =>
          exfalso
          rw [freshShiftAbove_ofLe threshold 2 a aGe, freshShiftAbove_ofNotLe threshold 2 b bLt] at shiftEq
          have bBelow : b < a + 2 :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_not_le bLt) aGe) (Nat.le_add_right a 2)
          rw [shiftEq] at bBelow
          exact Nat.lt_irrefl b bBelow
  | isFalse aLt =>
      cases Nat.decLe threshold b with
      | isTrue bGe =>
          exfalso
          rw [freshShiftAbove_ofNotLe threshold 2 a aLt, freshShiftAbove_ofLe threshold 2 b bGe] at shiftEq
          have aBelow : a < b + 2 :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_not_le aLt) bGe) (Nat.le_add_right b 2)
          rw [← shiftEq] at aBelow
          exact Nat.lt_irrefl a aBelow
      | isFalse bLt =>
          rw [freshShiftAbove_ofNotLe threshold 2 a aLt, freshShiftAbove_ofNotLe threshold 2 b bLt] at shiftEq
          exact shiftEq

/-- Mapping `freshShiftAbove threshold 2` over a list is injective. -/
private theorem mapFreshShiftInjective (threshold : Nat) : (first second : List Nat) →
    first.map (freshShiftAbove threshold 2) = second.map (freshShiftAbove threshold 2) → first = second
  | [], [], _ => rfl
  | [], headSecond :: restSecond, h => by
      have hcons : ([] : List Nat)
          = freshShiftAbove threshold 2 headSecond :: restSecond.map (freshShiftAbove threshold 2) := h
      injection hcons
  | headFirst :: restFirst, [], h => by
      have hcons : freshShiftAbove threshold 2 headFirst :: restFirst.map (freshShiftAbove threshold 2)
          = ([] : List Nat) := h
      injection hcons
  | headFirst :: restFirst, headSecond :: restSecond, h => by
      have hcons : freshShiftAbove threshold 2 headFirst :: restFirst.map (freshShiftAbove threshold 2)
          = freshShiftAbove threshold 2 headSecond :: restSecond.map (freshShiftAbove threshold 2) := h
      injection hcons with hHead hRest
      rw [freshShiftInjective threshold headFirst headSecond hHead,
        mapFreshShiftInjective threshold restFirst restSecond hRest]

/-- The right summand of a vanishing `Nat` sum is zero (a `noConfusion` peel). -/
private theorem addRightVanish : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → rightSummand = 0
  | _, 0, _ => rfl
  | _, _ + 1, sumZero => by rw [Nat.add_succ] at sumZero; exact Nat.noConfusion sumZero

private theorem addLeftVanish : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → leftSummand = 0
  | _, 0, sumZero => sumZero
  | _, _ + 1, sumZero => by rw [Nat.add_succ] at sumZero; exact Nat.noConfusion sumZero

/-- A cap-tally-free singleton atom is a cup (routed through the cap count, `propext`-free). -/
private theorem singletonCupArity {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget) (capZero : capAtomCount [atom] = 0) :
    atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2 := by
  cases adjunctionSpineAtom_isCupOrCap atom with
  | inl cupArity => exact cupArity
  | inr capArity =>
      exfalso
      have guardTrue : (atom.generatorDom.length == 2 && atom.generatorCod.length == 0) = true := by
        rw [capArity.1, capArity.2]; rfl
      dsimp only [capAtomCount] at capZero
      rw [if_pos guardTrue] at capZero
      exact Nat.noConfusion capZero

/-- The top-count field rises by exactly two through a top-of-stack cup (defeq to `natListInsertAt_length`). -/
private theorem topCount_stepCup (bottomCount : Nat) (state : WireState) (windowPosition : Nat) :
    (extractDiagram bottomCount (stepCup state windowPosition)).topCount
      = (extractDiagram bottomCount state).topCount + 2 :=
  natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]

/-- The partner list has length `bottomCount + openWires`. -/
private theorem extractDiagram_partner_length (bottomCount : Nat) (state : WireState) :
    (extractDiagram bottomCount state).partner.length = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length))).length = bottomCount + state.openWires.length
  rw [mapLength, rangeLength]

/-- Reduce a pure-cup boundary-chained spine `prefixAtoms ++ [lastCup]` at width `0` to a top-of-stack cup fired
onto the processed prefix, and supply the prefix state's shipped invariants (the plain analogue of the arc
`dropStepReduce`, specialised to the width-`0` seed where the seed-bound is `Nat.zero_le`). -/
private theorem dropStepReduce {overallSource overallTarget : adjunctionGraph.Mode}
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained 0 (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    matchingOfSpineList 0 (prefixAtoms ++ [lastCup])
        = extractDiagram 0
            (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length)
      ∧ WireStateFresh (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
      ∧ isUnionFindForest (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).links
      ∧ lastCup.leftContext.length ≤ (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length := by
  have lastCapZero : capAtomCount (prefixAtoms ++ [lastCup]) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ [lastCup]) pureCup
  have sumZero : capAtomCount prefixAtoms + capAtomCount [lastCup] = 0 :=
    (capAtomCount_append prefixAtoms [lastCup]).symm.trans lastCapZero
  obtain ⟨lastDom, lastCod⟩ := singletonCupArity lastCup (addRightVanish sumZero)
  have prefixPure : AllCupArity prefixAtoms := allCupArity_ofCapAtomCountZero prefixAtoms (addLeftVanish sumZero)
  have freshS : WireStateFresh (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) :=
    wireStateFresh_processSpine_ofAllCup prefixAtoms prefixPure ⟨List.range 0, [], 0, 0⟩ (wireStateFresh_initial 0)
  have forestS : isUnionFindForest (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).links :=
    isUnionFindForest_processSpine prefixAtoms ⟨List.range 0, [], 0, 0⟩ isUnionFindForest_nil
  have domLen := processSpine_prefix_openWires_eq_lastDomBoundary 0 prefixAtoms lastCup chained
  have windowFitsS : lastCup.leftContext.length
      ≤ (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length := by
    rw [domLen]
    show lastCup.leftContext.length
      ≤ lastCup.leftContext.length + lastCup.generatorDom.length + lastCup.rightContext.length
    exact Nat.le_trans (Nat.le_add_right lastCup.leftContext.length lastCup.generatorDom.length)
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length) lastCup.rightContext.length)
  have structEq : matchingOfSpineList 0 (prefixAtoms ++ [lastCup])
      = extractDiagram 0
          (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length) := by
    show extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ (prefixAtoms ++ [lastCup]))
      = extractDiagram 0
          (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length)
    rw [processSpine_append prefixAtoms [lastCup] ⟨List.range 0, [], 0, 0⟩]
    show extractDiagram 0 (stepAtom (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup)
      = extractDiagram 0
          (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length)
    rw [stepAtom_ofCupArity (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup lastDom lastCod]
  exact ⟨structEq, freshS, forestS, windowFitsS⟩

/-- ★ **Dropping a top-of-stack cup is matching-injective at width `0` (the S3 linchpin, plain carrier).**  If two
pure-cup boundary-chained spines over the width-`0` bottom boundary sharing a last cup have equal
`matchingOfSpineList 0`, then their prefixes do: the last cup fires LAST onto each processed prefix as a
top-of-stack cup, and each `DiagramType` field is a fixed injective image of the prefix's field
(`diagramPartner_stepCup` splices the short chord over the shift, `topCount` adds two, `bottomCount`/`loops` are
`rfl`).  The plain, 4-field analogue of `dropLastCup_arc_injective`. -/
theorem dropLastCup_matching_injective {overallSource overallTarget : adjunctionGraph.Mode}
    (firstPrefix secondPrefix : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chainedFirst : SpineBoundaryChained 0 (firstPrefix ++ [lastCup]))
    (chainedSecond : SpineBoundaryChained 0 (secondPrefix ++ [lastCup]))
    (pureCupFirst : AllCupArity (firstPrefix ++ [lastCup]))
    (pureCupSecond : AllCupArity (secondPrefix ++ [lastCup]))
    (appendedEqual : matchingOfSpineList 0 (firstPrefix ++ [lastCup])
      = matchingOfSpineList 0 (secondPrefix ++ [lastCup])) :
    matchingOfSpineList 0 firstPrefix = matchingOfSpineList 0 secondPrefix := by
  obtain ⟨structEqFirst, freshFirst, forestFirst, windowFitsFirst⟩ :=
    dropStepReduce firstPrefix lastCup chainedFirst pureCupFirst
  obtain ⟨structEqSecond, freshSecond, forestSecond, windowFitsSecond⟩ :=
    dropStepReduce secondPrefix lastCup chainedSecond pureCupSecond
  rw [structEqFirst, structEqSecond] at appendedEqual
  show extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)
    = extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)
  -- per-field inversions
  have eLoops : (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).loops
      = (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).loops := by
    have h := congrArg DiagramType.loops appendedEqual
    exact h
  have eBottom : (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).bottomCount
      = (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).bottomCount := rfl
  have eTop : (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).topCount
      = (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).topCount := by
    have h := congrArg DiagramType.topCount appendedEqual
    rw [topCount_stepCup, topCount_stepCup] at h
    exact addRightCancel 2 _ _ h
  have ePart : (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).partner
      = (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).partner := by
    have hMapEq : (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).partner.map
          (freshShiftAbove (0 + lastCup.leftContext.length) 2)
        = (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).partner.map
          (freshShiftAbove (0 + lastCup.leftContext.length) 2) := by
      apply natListInsertAt_leftInjective (0 + lastCup.leftContext.length)
        [0 + lastCup.leftContext.length + 1, 0 + lastCup.leftContext.length] _ _
        (by rw [mapLength, extractDiagram_partner_length]; exact Nat.add_le_add_left windowFitsFirst 0)
        (by rw [mapLength, extractDiagram_partner_length]; exact Nat.add_le_add_left windowFitsSecond 0)
      rw [← diagramPartner_stepCup 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)
          lastCup.leftContext.length freshFirst forestFirst (Nat.zero_le _) windowFitsFirst,
        ← diagramPartner_stepCup 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)
          lastCup.leftContext.length freshSecond forestSecond (Nat.zero_le _) windowFitsSecond]
      exact congrArg DiagramType.partner appendedEqual
    exact mapFreshShiftInjective (0 + lastCup.leftContext.length) _ _ hMapEq
  show DiagramType.mk
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).bottomCount
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).topCount
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).partner
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).loops
    = DiagramType.mk
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).bottomCount
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).topCount
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).partner
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).loops
  rw [eBottom, eTop, ePart, eLoops]

end FX1Poly.Polygraph
