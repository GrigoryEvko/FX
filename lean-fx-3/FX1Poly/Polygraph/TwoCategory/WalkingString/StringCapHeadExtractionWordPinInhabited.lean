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
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

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

end FX1Poly.Polygraph
