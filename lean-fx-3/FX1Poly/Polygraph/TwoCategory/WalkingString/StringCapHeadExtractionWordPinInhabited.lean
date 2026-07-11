import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapHeadExtractionWordPinPrime
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordPairSeatedDescentOfDistinct
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapHeadTransport
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapHeadCancellation
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcSwapPeel
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapWindowSeedReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordBubble
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordFactorization
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcWireDistinct
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairUntouched
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff

/-! # WalkingString/StringCapHeadExtractionWordPinInhabited — inhabiting the AllCapArity-augmented cap-head
pin-prime (FC-3 r26)

The r25 pin-prime file (`StringCapHeadExtractionWordPinPrime`) shipped the AllCapArity-augmented cap-head
discharge Prop and re-wired the peel-first pure-cap sort to consume it, leaving the four-conjunct assembly of
`StringCapHeadExtractionWordPinPrime` as the standing r26 obligation.  This file assembles that inhabitant, a
direct port of the walking-adjunction mirror `spineArcHeadExtractionChained_ofCapArity`
(`WalkingAdjunction/ArcCapHeadDischarge`) with the length-rigid identify swapped for the DOM word pin
(`stringCapAtom_eq_of_sharedDom_sameWindow`) and the word-chain conjunct (3) threaded through the WORD bubble:

  * LOCATE — arc-structure equality transports the cap-head window onto the second spine
    (`stringArcPairCapWindow_ofCapHeadExtractEq`), producing the `StringArcPairCapWindow` certificate;
  * SEAT + DESCEND — the located cap seats at the seed and bubbles to the front through the re-founded
    distinctness descent master (`stringWordPairSeated_bubblesThroughPrefix_ofDistinct`, B2), the string clone
    of the adjunction's `bubblesToFront_ofArcPairCapWindow`;
  * IDENTIFY — the moved atom is the head cap by the DOM word pin (both fire at `bottomWord`);
  * REALIZE + CANCEL — the WORD bubble consumers (`spineTraceEquiv_of_wordBubblesToFront`,
    `spineBoundaryWordChained_of_wordBubblesToFront`, `spineBoundaryChained_ofWordChained`) close conjuncts
    1/3/2, and the r21 cancel (`stringArcCapHeadFolded_extractArc_cancel`) fed the pin-prime's `AllCapArity`
    closes conjunct 4.

Raw Lean 4 + Init; structural on the prefix list where fresh recursion is needed.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range read plumbing (private copy — the seed files' kits are file-private) -/

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

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) →
    (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

/-! ## Micro-brick G-a — `AllCapArity` prefix-of-append inversion -/

/-- ★ **A pure-cap append's prefix is pure cap.**  The `AllCapArity` analog of the shipped cup twin
`allCupArity_prefix_ofAppend`: peel the head cap off the append and recurse on the prefix, rebuilding
`AllCapArity (headAtom :: restPrefix)`.  Routed through `stringAllCapArity_ofCons` at each peel (the
`propext`-free cup-count inversion), so a direct `cases` on the head-indexed `AllCapArity` is avoided.  Supplies
`AllCapArity prefixAtoms` at the descent's top-level premise from the second spine's `AllCapArity`. -/
theorem stringAllCapArity_prefix_ofAppend
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (prefixAtoms suffixAtoms :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    AllCapArity (prefixAtoms ++ suffixAtoms) → AllCapArity prefixAtoms
  | [], _, _ => AllCapArity.nil
  | headAtom :: restPrefix, suffixAtoms, appendPureCap => by
      obtain ⟨headDom, headCod⟩ := stringHeadCapArity appendPureCap
      have restAppendPureCap : AllCapArity (restPrefix ++ suffixAtoms) :=
        stringAllCapArity_ofCons appendPureCap
      exact AllCapArity.cons headDom headCod
        (stringAllCapArity_prefix_ofAppend restPrefix suffixAtoms restAppendPureCap)

/-! ## Order-preservation of the pure-cap split open-wires (closes the swapped-read branch)

The located certificate's `doesConsumePair` is a two-order disjunction; the SWAPPED order (the toucher's window
reading `rightIndex` then `leftIndex`) cannot feed the re-founded descent master, whose `∃ seatBefore` premise
is unsatisfiable for the reversed pair at the seed.  It is refuted by order-preservation: a pure-cap fold from
the sorted `range` seed keeps `openWires` adjacently strictly increasing, so the toucher's two consecutive reads
are in increasing order — contradicting the swapped read of the two consecutive seed ports. -/

/-- **A pair removal preserves adjacent strict increase.**  Removing the two-wire window at `windowPosition`
(in range) from an adjacently-strictly-increasing list keeps it adjacently strictly increasing: below the
window reads are untouched, past it reads shift down by two, and at the seam the removed pair is bridged by
transitivity through the three original adjacent steps. -/
private theorem natListRemoveTwoAt_adjIncreasing
    (wires : List Nat) (windowPosition : Nat)
    (windowFits : windowPosition + 2 ≤ wires.length)
    (increasing : ∀ position, position + 1 < wires.length →
      natListGetAt wires position < natListGetAt wires (position + 1)) :
    ∀ position, position + 1 < (natListRemoveTwoAt wires windowPosition).length →
      natListGetAt (natListRemoveTwoAt wires windowPosition) position
        < natListGetAt (natListRemoveTwoAt wires windowPosition) (position + 1) := by
  intro position positionInRange
  have removedLen : (natListRemoveTwoAt wires windowPosition).length + 2 = wires.length :=
    natListRemoveTwoAt_length wires windowPosition windowFits
  have windowBelowWires : windowPosition < wires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_succ windowPosition)) windowFits
  have windowSuccBelowWires : windowPosition + 1 < wires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (windowPosition + 1)) windowFits
  -- position + 3 ≤ wires.length from positionInRange (position + 1 < removed.length, removed.length + 2 = wires.length)
  have positionSuccPlusTwo : position + 1 + 2 < wires.length := by
    have shifted : position + 1 + 2 < (natListRemoveTwoAt wires windowPosition).length + 2 :=
      Nat.add_lt_add_right positionInRange 2
    rw [removedLen] at shifted
    exact shifted
  cases Nat.lt_or_ge position windowPosition with
  | inl belowWindow =>
      cases Nat.lt_or_ge (position + 1) windowPosition with
      | inl succBelowWindow =>
          rw [natListGetAt_natListRemoveTwoAt_below wires windowPosition position belowWindow,
            natListGetAt_natListRemoveTwoAt_below wires windowPosition (position + 1) succBelowWindow]
          exact increasing position (Nat.lt_trans succBelowWindow windowBelowWires)
      | inr succAtLeastWindow =>
          have succEqWindow : position + 1 = windowPosition :=
            Nat.le_antisymm (Nat.succ_le_of_lt belowWindow) succAtLeastWindow
          rw [natListGetAt_natListRemoveTwoAt_below wires windowPosition position belowWindow]
          have pastRead : natListGetAt (natListRemoveTwoAt wires windowPosition) (windowPosition + 0)
              = natListGetAt wires (windowPosition + 0 + 2) :=
            natListGetAt_natListRemoveTwoAt_pastPair wires windowPosition 0 windowFits
          rw [Nat.add_zero] at pastRead
          rw [succEqWindow, pastRead]
          -- goal: wires[position] < wires[windowPosition + 2]
          have stepOne : natListGetAt wires position < natListGetAt wires (position + 1) :=
            increasing position (succEqWindow ▸ windowBelowWires)
          have stepTwo : natListGetAt wires windowPosition
              < natListGetAt wires (windowPosition + 1) :=
            increasing windowPosition windowSuccBelowWires
          have windowPlusTwoBelow : windowPosition + 2 < wires.length := succEqWindow ▸ positionSuccPlusTwo
          have windowSuccSuccBelow : windowPosition + 1 + 1 < wires.length := windowPlusTwoBelow
          have stepThree : natListGetAt wires (windowPosition + 1)
              < natListGetAt wires (windowPosition + 1 + 1) :=
            increasing (windowPosition + 1) windowSuccSuccBelow
          rw [succEqWindow] at stepOne
          exact Nat.lt_trans stepOne (Nat.lt_trans stepTwo stepThree)
  | inr atLeastWindow =>
      obtain ⟨gap, gapEq⟩ := Nat.le.dest atLeastWindow
      have readAtPosition : natListGetAt (natListRemoveTwoAt wires windowPosition) position
          = natListGetAt wires (position + 2) := by
        have pastRead := natListGetAt_natListRemoveTwoAt_pastPair wires windowPosition gap windowFits
        rw [gapEq] at pastRead
        exact pastRead
      have readAtSucc : natListGetAt (natListRemoveTwoAt wires windowPosition) (position + 1)
          = natListGetAt wires (position + 1 + 2) := by
        have pastRead := natListGetAt_natListRemoveTwoAt_pastPair wires windowPosition (gap + 1)
          windowFits
        rw [show windowPosition + (gap + 1) = position + 1 by rw [← Nat.add_assoc, gapEq]] at pastRead
        exact pastRead
      rw [readAtPosition, readAtSucc]
      have adjacentPast : natListGetAt wires (position + 2) < natListGetAt wires (position + 2 + 1) :=
        increasing (position + 2) (by rw [Nat.add_right_comm position 2 1]; exact positionSuccPlusTwo)
      rw [Nat.add_right_comm position 2 1] at adjacentPast
      exact adjacentPast

/-- **The pure-cap fold from an adjacently-increasing state stays adjacently increasing.**  Structural on the
prefix: every atom is a cap (`stringHeadCapArity`), whose step is a pair removal (`stepArcAtom_eq_stepCapArc`) at
an in-range window (the boundary chain gives the window fit), and pair removal preserves adjacent strict increase
(`natListRemoveTwoAt_adjIncreasing`); the boundary chain advances via `stepArcAtom_openWires_tracksBoundary`. -/
private theorem stringCapFoldAdjIncreasing
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → AllCapArity prefixAtoms →
    SpineBoundaryChained state.openWires.length prefixAtoms →
    (∀ position, position + 1 < state.openWires.length →
      natListGetAt state.openWires position < natListGetAt state.openWires (position + 1)) →
    ∀ position, position + 1 < (processArcSpine state prefixAtoms).openWires.length →
      natListGetAt (processArcSpine state prefixAtoms).openWires position
        < natListGetAt (processArcSpine state prefixAtoms).openWires (position + 1)
  | [], _, _, _, increasing => increasing
  | capAtom :: restPrefix, state, allCap, chained, increasing => by
      obtain ⟨domTwo, codZero⟩ := stringHeadCapArity allCap
      have allCapRest : AllCapArity restPrefix := stringAllCapArity_ofCons allCap
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have entryShape : state.openWires.length
          = capAtom.leftContext.length + capAtom.generatorDom.length
            + capAtom.rightContext.length := headFires.symm
      have windowFits : capAtom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, domTwo]
        exact Nat.le_add_right (capAtom.leftContext.length + 2) capAtom.rightContext.length
      have stepIsCap : stepArcAtom state capAtom
          = stepCapArc state capAtom.leftContext.length :=
        stepArcAtom_eq_stepCapArc state capAtom domTwo codZero
      have steppedIncreasing : ∀ position,
          position + 1 < (stepArcAtom state capAtom).openWires.length →
          natListGetAt (stepArcAtom state capAtom).openWires position
            < natListGetAt (stepArcAtom state capAtom).openWires (position + 1) := by
        rw [stepIsCap]
        exact natListRemoveTwoAt_adjIncreasing state.openWires capAtom.leftContext.length windowFits
          increasing
      have stepTracks : (stepArcAtom state capAtom).openWires.length = capAtom.codBoundaryLength :=
        stepArcAtom_openWires_tracksBoundary state capAtom
          (adjointTripleSpineAtom_hasCupOrCapArity capAtom) headFires.symm
      have steppedChained : SpineBoundaryChained (stepArcAtom state capAtom).openWires.length
          restPrefix := stepTracks ▸ tailChained
      exact stringCapFoldAdjIncreasing restPrefix (stepArcAtom state capAtom) allCapRest
        steppedChained steppedIncreasing

/-- **The initial seed open-wires are adjacently strictly increasing.**  `natListGetAt (range n) position
= position`, so consecutive reads step up by one. -/
private theorem rangeAdjIncreasing (bottomCount : Nat) :
    ∀ position, position + 1 < (List.range bottomCount).length →
      natListGetAt (List.range bottomCount) position
        < natListGetAt (List.range bottomCount) (position + 1) := by
  intro position positionInRange
  rw [rangeLength bottomCount] at positionInRange
  have positionBelow : position < bottomCount :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self position) (Nat.le_of_lt positionInRange)
  rw [rangeGetAt_below bottomCount position positionBelow,
    rangeGetAt_below bottomCount (position + 1) positionInRange]
  exact Nat.lt_succ_self position

/-! ## Truth-probes (anti-vacuity, concrete `ε` at `tip`) -/

/-- ★ **Seat/range probe.**  The tracked seed pair `(0, 1)` is seated adjacent at position `0` in the two-wire
seed `range 2`, and the range read-off `natListGetAt (range 2) 0 = 0` fires — the seat glue the LOCATE brick
builds at the seed, machine-checked on the concrete two-wire valley the lower counit `ε` (dom length `2`, window
`0`) consumes. -/
theorem stringInhabitSeatProbe :
    ArcPairSeated 0 1 0 (ArcWireState.mk (List.range 2) [] 2 0 [] [])
      ∧ natListGetAt (List.range 2) 0 = 0 :=
  ⟨⟨by decide, by decide, by decide⟩, rangeGetAt_below 2 0 (by decide)⟩

/-- ★ **The prefix-inversion probe fires on the three-cap spine.**  Splitting the concrete three-cap spine as
`[ε] ++ [ε, ε]` and inverting recovers `AllCapArity [ε]` — the micro-brick G-a end-to-end on a genuine multi-cap
prefix. -/
theorem stringInhabitPrefixInversionProbe :
    AllCapArity [stringCapSortProbeAtom] :=
  stringAllCapArity_prefix_ofAppend [stringCapSortProbeAtom]
    [stringCapSortProbeAtom, stringCapSortProbeAtom] stringProbeThreeCap_allCap

/-- ★ **G-b probe — the seed open-wire count.**  The empty pure-cap fold from the two-wire seed keeps its two
open wires, and a one-cap fold at window `0` drops to zero — the boundary the seat bound
(`stringArcPairCapWindow_splitSeatBound`) tracks, checked concretely. -/
theorem stringInhabitBoundaryProbe :
    (processArcSpine (ArcWireState.mk (List.range 2) [] 2 0 [] [])
      ([] : List (SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip))).openWires.length = 2
      ∧ (processArcSpine (ArcWireState.mk (List.range 2) [] 2 0 [] [])
          [stringCapSortProbeAtom]).openWires.length = 0 :=
  ⟨by decide, by decide⟩

/-! ## The pin-prime inhabitant -/

/-- ★★ **The AllCapArity-augmented cap-head pin-prime is inhabited.**  Assembles the four-conjunct discharge, the
port of `spineArcHeadExtractionChained_ofCapArity` with the DOM word pin and the threaded word chain: arc-structure
equality LOCATES the consuming cap in the second spine (`stringArcPairCapWindow_ofCapHeadExtractEq`), the located
cap SEATS at the seed and BUBBLES to the front through the re-founded distinctness descent
(`stringWordPairSeated_bubblesThroughPrefix_ofDistinct`), the moved atom IDENTIFIES with the head by the DOM word
pin (`stringCapAtom_eq_of_sharedDom_sameWindow`, both firing at `bottomWord`), and the WORD-bubble consumers plus
the r21 cancel close the four conjuncts.  The swapped-read branch of the located certificate is refuted by
order-preservation of the pure-cap split open-wires (`stringCapFoldAdjIncreasing`). -/
theorem stringCapHeadExtractionWordPinInhabited : StringCapHeadExtractionWordPinPrime := by
  intro overallSource overallTarget bottomCount bottomWord headAtom c1Dom c1Cod tailList secondList
    chainedFirst chainedSecond firstWordChained secondWordChained firstPureCap secondPureCap arcEqual
  obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chainedFirst
  have windowFits : headAtom.leftContext.length + 2 ≤ bottomCount := by
    rw [← headFires]
    show headAtom.leftContext.length + 2
      ≤ headAtom.leftContext.length + headAtom.generatorDom.length + headAtom.rightContext.length
    rw [c1Dom]
    exact Nat.le_add_right (headAtom.leftContext.length + 2) headAtom.rightContext.length
  have tailBoundaryFits : headAtom.codBoundaryLength + 2 = bottomCount := by
    rw [← headFires]
    show headAtom.leftContext.length + headAtom.generatorCod.length + headAtom.rightContext.length + 2
      = headAtom.leftContext.length + headAtom.generatorDom.length + headAtom.rightContext.length
    rw [c1Cod, c1Dom]
    exact Nat.add_right_comm headAtom.leftContext.length headAtom.rightContext.length 2
  have extractEq : extractArc bottomCount
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          headAtom.leftContext.length) tailList)
      = extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            secondList) := by
    rw [← stepArcAtom_eq_stepCapArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) headAtom c1Dom c1Cod]
    exact arcEqual
  have located : StringArcPairCapWindow bottomCount headAtom.leftContext.length
      (headAtom.leftContext.length + 1) secondList :=
    stringArcPairCapWindow_ofCapHeadExtractEq bottomCount headAtom.leftContext.length
      headAtom.codBoundaryLength windowFits tailBoundaryFits tailList tailChained secondList extractEq
  obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplitSpine, untouchedBefore, capDomArity,
    capCodArity, doesConsumePair⟩ := located
  have leftBelow : headAtom.leftContext.length < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self headAtom.leftContext.length)
        (Nat.lt_succ_self (headAtom.leftContext.length + 1)))
      windowFits
  have rightBelow : headAtom.leftContext.length + 1 < bottomCount :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (headAtom.leftContext.length + 1)) windowFits
  have seatBefore : ∃ seatPosition,
      ArcPairSeated headAtom.leftContext.length (headAtom.leftContext.length + 1) seatPosition
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) :=
    ⟨headAtom.leftContext.length,
      rangeGetAt_below bottomCount headAtom.leftContext.length leftBelow,
      rangeGetAt_below bottomCount (headAtom.leftContext.length + 1) rightBelow, by
        show headAtom.leftContext.length + 2 ≤ (List.range bottomCount).length
        rw [rangeLength bottomCount]; exact windowFits⟩
  have chainedAtSeed : SpineBoundaryChained
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []).openWires.length
      (prefixAtoms ++ toucherAtom :: suffixAtoms) := by
    show SpineBoundaryChained (List.range bottomCount).length
      (prefixAtoms ++ toucherAtom :: suffixAtoms)
    rw [rangeLength bottomCount, ← doesSplitSpine]
    exact chainedSecond
  have allCapPrefix : AllCapArity prefixAtoms :=
    stringAllCapArity_prefix_ofAppend prefixAtoms (toucherAtom :: suffixAtoms)
      (doesSplitSpine ▸ secondPureCap)
  have prefixChain : SpineBoundaryChained
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []).openWires.length
      prefixAtoms :=
    spineBoundaryChained_prefix_ofAppend prefixAtoms (toucherAtom :: suffixAtoms)
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []).openWires.length chainedAtSeed
  have chainedAtSplit : SpineBoundaryChained
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        prefixAtoms).openWires.length (toucherAtom :: suffixAtoms) :=
    stringSpineBoundaryChained_alongArcSpine prefixAtoms (toucherAtom :: suffixAtoms)
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) chainedAtSeed
  have splitEntryShape : (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      prefixAtoms).openWires.length
      = toucherAtom.leftContext.length + toucherAtom.generatorDom.length
        + toucherAtom.rightContext.length :=
    (spineBoundaryChained_tail chainedAtSplit).1.symm
  have seatBound : toucherAtom.leftContext.length + 2
      ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        prefixAtoms).openWires.length := by
    rw [splitEntryShape, capDomArity]
    exact Nat.le_add_right (toucherAtom.leftContext.length + 2) toucherAtom.rightContext.length
  have wordChainedRemainder : SpineBoundaryWordChained bottomWord
      (prefixAtoms ++ toucherAtom :: suffixAtoms) := doesSplitSpine ▸ secondWordChained
  cases doesConsumePair with
  | inr swappedReads =>
      exfalso
      have splitIncreasing := stringCapFoldAdjIncreasing prefixAtoms
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) allCapPrefix prefixChain
        (rangeAdjIncreasing bottomCount) toucherAtom.leftContext.length
        (Nat.lt_of_succ_le seatBound)
      rw [swappedReads.1, swappedReads.2] at splitIncreasing
      exact Nat.lt_irrefl headAtom.leftContext.length
        (Nat.lt_trans (Nat.lt_succ_self headAtom.leftContext.length) splitIncreasing)
  | inl orderedReads =>
      have seatedEnd : ArcPairSeated headAtom.leftContext.length (headAtom.leftContext.length + 1)
          toucherAtom.leftContext.length
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) :=
        ⟨orderedReads.1, orderedReads.2, seatBound⟩
      obtain ⟨movedTarget, movedPrefixAtoms, witness, movedDom, movedCod, movedSeat, _parity⟩ :=
        stringWordPairSeated_bubblesThroughPrefix_ofDistinct toucherAtom capDomArity capCodArity
          suffixAtoms headAtom.leftContext.length (headAtom.leftContext.length + 1) prefixAtoms
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomWord
          (arcStateFresh_initial bottomCount) (arcInitialState_wireListDistinct bottomCount)
          (arcPairUntouched_initial bottomCount headAtom.leftContext.length
            (headAtom.leftContext.length + 1) leftBelow rightBelow)
          seatBefore allCapPrefix chainedAtSeed wordChainedRemainder seatedEnd
      have movedSeatWindowBound : movedTarget.leftContext.length + 2 ≤ (List.range bottomCount).length :=
        movedSeat.2.2
      rw [rangeLength bottomCount] at movedSeatWindowBound
      have movedWindowBelow : movedTarget.leftContext.length < bottomCount :=
        Nat.lt_of_lt_of_le
          (Nat.lt_trans (Nat.lt_succ_self movedTarget.leftContext.length)
            (Nat.lt_succ_self (movedTarget.leftContext.length + 1)))
          movedSeatWindowBound
      have windowPin : movedTarget.leftContext.length = headAtom.leftContext.length :=
        (rangeGetAt_below bottomCount movedTarget.leftContext.length movedWindowBelow).symm.trans
          movedSeat.1
      have bubbledWord : SpineBoundaryWordChained bottomWord
          (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) :=
        spineBoundaryWordChained_of_wordBubblesToFront witness suffixAtoms wordChainedRemainder
      have movedIsHead : movedTarget = headAtom :=
        stringCapAtom_eq_of_sharedDom_sameWindow movedTarget headAtom
          ((spineBoundaryWordChained_tail bubbledWord).1.symm.trans
            (spineBoundaryWordChained_tail firstWordChained).1)
          windowPin movedDom c1Dom
      -- conjunct (1): the bubbled second spine realizes the head-consed remainder
      have conjunct1 : SpineTraceEquiv adjointTripleModeSignature secondList
          (headAtom :: (movedPrefixAtoms ++ suffixAtoms)) := by
        rw [doesSplitSpine, ← movedIsHead]
        exact spineTraceEquiv_of_wordBubblesToFront witness suffixAtoms
      -- conjunct (3): the remainder is word-chained at the head cap's cod word
      have conjunct3 : SpineBoundaryWordChained
          (composePath headAtom.leftContext
            (composePath headAtom.generatorCod headAtom.rightContext))
          (movedPrefixAtoms ++ suffixAtoms) := by
        have rawWordChained := (spineBoundaryWordChained_tail bubbledWord).2
        rw [movedIsHead] at rawWordChained
        exact rawWordChained
      -- conjunct (2): the remainder is length-chained at the shrunk boundary
      have codLenEq : (composePath headAtom.leftContext
            (composePath headAtom.generatorCod headAtom.rightContext)).length
          = headAtom.codBoundaryLength := by
        dsimp only [SpineAtom.codBoundaryLength]
        rw [composePath_length, composePath_length]
        exact (Nat.add_assoc headAtom.leftContext.length headAtom.generatorCod.length
          headAtom.rightContext.length).symm
      have conjunct2 : SpineBoundaryChained headAtom.codBoundaryLength
          (movedPrefixAtoms ++ suffixAtoms) :=
        codLenEq ▸ spineBoundaryChained_ofWordChained conjunct3
      -- conjunct (4): the two tails have equal arc structure at the shrunk boundary
      have atomicEquiv : AtomicTraceEquiv adjointTripleModeSignature secondList
          (headAtom :: (movedPrefixAtoms ++ suffixAtoms)) := by
        rw [doesSplitSpine, ← movedIsHead]
        exact atomicTraceEquiv_of_wordBubblesToFront witness suffixAtoms
      have hasPositiveWidth : 0 < bottomCount :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ (headAtom.leftContext.length + 1)) windowFits
      have traceEquivArc : arcStructureOfSpineList bottomCount secondList
          = arcStructureOfSpineList bottomCount (headAtom :: (movedPrefixAtoms ++ suffixAtoms)) :=
        extractArc_eq_of_stringAtomicTraceEquiv atomicEquiv
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
          (arcStateFresh_initial bottomCount) (isUnionFindForest_initialLinks bottomCount)
          hasPositiveWidth (Nat.le_refl bottomCount) (rangeLength bottomCount) chainedSecond
      have consPure : AllCapArity (headAtom :: (movedPrefixAtoms ++ suffixAtoms)) :=
        stringAllCapArity_ofArcEqualToPureCap bottomCount secondList
          (headAtom :: (movedPrefixAtoms ++ suffixAtoms)) secondPureCap traceEquivArc
      have matchedPure : AllCapArity (movedPrefixAtoms ++ suffixAtoms) :=
        stringAllCapArity_ofCons consPure
      have tailAllCap : AllCapArity tailList := stringAllCapArity_ofCons firstPureCap
      have wholeAgree : arcStructureOfSpineList bottomCount (headAtom :: tailList)
          = arcStructureOfSpineList bottomCount (headAtom :: (movedPrefixAtoms ++ suffixAtoms)) :=
        arcEqual.trans traceEquivArc
      have compositeAgree : extractArc bottomCount
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              headAtom.leftContext.length) tailList)
          = extractArc bottomCount
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  headAtom.leftContext.length) (movedPrefixAtoms ++ suffixAtoms)) := by
        rw [← stepArcAtom_eq_stepCapArc
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) headAtom c1Dom c1Cod]
        exact wholeAgree
      have conjunct4 : arcStructureOfSpineList headAtom.codBoundaryLength tailList
          = arcStructureOfSpineList headAtom.codBoundaryLength (movedPrefixAtoms ++ suffixAtoms) :=
        stringArcCapHeadFolded_extractArc_cancel bottomCount headAtom.leftContext.length
          headAtom.codBoundaryLength windowFits tailBoundaryFits tailList
          (movedPrefixAtoms ++ suffixAtoms) tailAllCap matchedPure tailChained conjunct2
          compositeAgree
      exact ⟨movedPrefixAtoms ++ suffixAtoms, conjunct1, conjunct2, conjunct3, conjunct4⟩

end FX1Poly.Polygraph
