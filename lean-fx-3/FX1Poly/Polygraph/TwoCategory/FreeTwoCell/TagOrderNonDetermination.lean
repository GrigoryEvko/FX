import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TraceNormalFormNonInvariance
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TaggedReplay
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SaturationFuelBound
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SaturationDecisionSmoke

/-! # TagOrderNonDetermination — ★★ tag order does NOT determine the class member

THE FINDING.  The FREE-7 determination conjecture — reachable tagged traces with equal
tag lists are equal — is FALSE, and with it the completeness of the tag-order candidate
enumeration (`classEnumerationCandidate`).  The witness is the shipped Eckmann–Hilton
bubble: tag the creation 0 and the bubble 1; then

  * `[⟨0, creation⟩, ⟨1, bubble RIGHT of strand⟩]` and
  * `[⟨0, creation⟩, ⟨1, bubble LEFT  of strand⟩]`

are `TaggedTraceEquiv` (un-fire the creation, float the bubble through its nil source
boundary, re-fire the creation on the bubble's other side — the two-swap zigzag through
`[⟨1, bubble at origin⟩, ⟨0, creation⟩]`), carry the SAME tag list `[0, 1]` — dup-free —
yet differ as traces: the bubble's whisker contexts remember WHICH SIDE of the strand it
floats on, and the tag order cannot see the side.

Consequences, both mechanized here:

  * ★★ `tagOrder_doesNotDetermineClassMember` — the determination lemma is dead as
    stated; no strengthening that only reads the tag order can pin the member;
  * ★★ `classEnumerationCandidate_isNotComplete` — replay enumerates AT MOST ONE member
    per tag order, so the slid trace is unreachable by replay from the seed: the n^n
    tag-order enumeration is provably NOT a complete class list (computed: the candidate
    list is exactly `[source, target]`, missing the slid member).

ROUTE CONSEQUENCE.  FREE-7's unconditional decider cannot be completed through tag-order
replay.  The class-saturation BFS decider (`decideAtomicTraceEquivViaSaturation`) remains
sound and per-seed complete whenever its frontier exhausts (the bubble class itself
exhausts within fuel 16 — `bubbleSaturationExhausts`); what is missing is a UNIVERSAL
fuel bound, i.e. class finiteness.  The corrected route is a BOUNDED ATOM UNIVERSE:
contexts of reachable atoms are paths over the seed's finite letter alphabet with
swap-invariant length bounds, so the finite list of all bounded-context traces is a
complete class list — an invariant argument, not a determination argument.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The tagged witness traces -/

/-- The tagged seed: creation tagged 0, then the bubble tagged 1 floating RIGHT of the
strand. -/
def taggedBubbleSourceTrace :
    List (TaggedSpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode) :=
  [⟨0, bubbleCreationAtom⟩, ⟨1, bubbleRightOfStrandAtom⟩]

/-- The zigzag midpoint: the bubble (tag 1) fires first at the origin, the creation
(tag 0) after it. -/
def taggedBubbleMiddleTrace :
    List (TaggedSpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode) :=
  [⟨1, bubbleAtOriginAtom⟩, ⟨0, bubbleCreationAtom⟩]

/-- The slid endpoint: SAME tag order as the seed — creation 0 first, bubble 1 second —
but the bubble now floats LEFT of the strand. -/
def taggedBubbleSlidTrace :
    List (TaggedSpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode) :=
  [⟨0, bubbleCreationAtom⟩, ⟨1, bubbleLeftOfStrandAtom⟩]

/-- First zigzag leg: the bubble crosses the creation leftward (the shipped source
witness, tags riding). -/
theorem taggedBubbleFirstSwap :
    TaggedSpineAtomSwap bubbleSignature taggedBubbleSourceTrace taggedBubbleMiddleTrace :=
  bubbleSourceSwapWitness.toTaggedSwap 0 1 []

/-- Second zigzag leg: the creation crosses the bubble leftward, landing the bubble on
the strand's OTHER side (the shipped repeat witness, tags riding). -/
theorem taggedBubbleSecondSwap :
    TaggedSpineAtomSwap bubbleSignature taggedBubbleMiddleTrace taggedBubbleSlidTrace :=
  bubbleRepeatSwapWitness.toTaggedSwap 1 0 []

/-! ## ★★ The falsification: equal tag lists, equivalent, unequal -/

/-- The seed and the slid trace are tagged-trace equivalent — the two-swap Eckmann–Hilton
zigzag. -/
theorem taggedBubbleTraces_areEquivalent :
    TaggedTraceEquiv bubbleSignature taggedBubbleSourceTrace taggedBubbleSlidTrace :=
  TaggedTraceEquiv.trans (TaggedTraceEquiv.ofSwap taggedBubbleFirstSwap)
    (TaggedTraceEquiv.ofSwap taggedBubbleSecondSwap)

/-- Both traces carry the tag list `[0, 1]` — the same dup-free tag order. -/
theorem taggedBubbleTraces_haveEqualTagLists :
    spineTagList taggedBubbleSourceTrace = spineTagList taggedBubbleSlidTrace := rfl

/-- The traces differ: the bubble's left context is the strand on one side and empty on
the other. -/
theorem taggedBubbleTraces_areNotEqual :
    taggedBubbleSourceTrace ≠ taggedBubbleSlidTrace := by
  intro tracesEqual
  have literalListsEqual : [(⟨0, bubbleCreationAtom⟩ :
        TaggedSpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode),
        ⟨1, bubbleRightOfStrandAtom⟩]
      = [⟨0, bubbleCreationAtom⟩, ⟨1, bubbleLeftOfStrandAtom⟩] := tracesEqual
  injection literalListsEqual with _ tailsEqual
  injection tailsEqual with taggedAtomsEqual _
  have atomsEqual : bubbleRightOfStrandAtom = bubbleLeftOfStrandAtom :=
    congrArg TaggedSpineAtom.atom taggedAtomsEqual
  have lengthClash : (1 : Nat) = 0 :=
    congrArg (fun atom => atom.leftContext.length) atomsEqual
  exact Nat.noConfusion lengthClash

/-- ★★ **Tag order does not determine the class member**: two tagged traces, equivalent,
with equal (dup-free) tag lists, that are not equal.  The FREE-7 determination rung is
FALSE as stated. -/
theorem tagOrder_doesNotDetermineClassMember :
    ∃ (firstList secondList :
        List (TaggedSpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode)),
      TaggedTraceEquiv bubbleSignature firstList secondList
        ∧ spineTagList firstList = spineTagList secondList
        ∧ firstList ≠ secondList :=
  ⟨taggedBubbleSourceTrace, taggedBubbleSlidTrace, taggedBubbleTraces_areEquivalent,
    taggedBubbleTraces_haveEqualTagLists, taggedBubbleTraces_areNotEqual⟩

/-! ## ★★ The corollary: the tag-order candidate enumeration is not complete -/

/-- The slid trace, untagged: creation first, the bubble LEFT of the strand. -/
def bubbleSlidTrace :
    List (SpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode) :=
  [bubbleCreationAtom, bubbleLeftOfStrandAtom]

/-- The slid trace is in the seed's class (the untagged Eckmann–Hilton zigzag). -/
theorem bubbleSlidTrace_isEquivalentToSeed :
    AtomicTraceEquiv bubbleSignature bubbleSourceTrace bubbleSlidTrace :=
  AtomicTraceEquiv.trans (AtomicTraceEquiv.ofSwap bubbleSwapStep)
    (AtomicTraceEquiv.ofSwap bubbleRepeatSwapStep)

/-- The candidate enumeration on the bubble seed computes to exactly the seed and the
one-swap target — the slid member never appears, because replay reconstructs AT MOST ONE
trace per tag order. -/
theorem bubbleClassEnumerationComputes :
    classEnumerationCandidate bubbleModeDecEq bubbleModalityDecEq bubbleSourceTrace
      = [bubbleSourceTrace, bubbleTargetTrace] := rfl

/-- The slid trace is fresh against the computed candidate list (decidable equality
computes: it differs from the seed in the bubble's contexts and from the target in the
leading generator). -/
theorem bubbleSlidTrace_isFreshAgainstCandidates :
    isFreshAgainst (spineListDecEq bubbleModeDecEq bubbleModalityDecEq bubbleTwoCellDecEq)
      [bubbleSourceTrace, bubbleTargetTrace] bubbleSlidTrace = true := rfl

/-- The slid trace is NOT enumerated by the tag-order replay. -/
theorem bubbleSlidTrace_isNotEnumerated :
    ¬ (bubbleSlidTrace
        ∈ classEnumerationCandidate bubbleModeDecEq bubbleModalityDecEq
            bubbleSourceTrace) := by
  intro memberMem
  have memberMemComputed : bubbleSlidTrace ∈ [bubbleSourceTrace, bubbleTargetTrace] :=
    bubbleClassEnumerationComputes ▸ memberMem
  exact notMem_ofIsFreshAgainst
    (spineListDecEq bubbleModeDecEq bubbleModalityDecEq bubbleTwoCellDecEq)
    bubbleSlidTrace_isFreshAgainstCandidates memberMemComputed

/-- ★★ **The tag-order candidate enumeration is not complete**: a class member the
replay enumeration misses.  `classEnumerationCandidate` cannot serve as the complete
class list of the unconditional decider. -/
theorem classEnumerationCandidate_isNotComplete :
    ∃ (seedAtoms member :
        List (SpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode)),
      AtomicTraceEquiv bubbleSignature seedAtoms member
        ∧ ¬ (member ∈ classEnumerationCandidate bubbleModeDecEq bubbleModalityDecEq
              seedAtoms) :=
  ⟨bubbleSourceTrace, bubbleSlidTrace, bubbleSlidTrace_isEquivalentToSeed,
    bubbleSlidTrace_isNotEnumerated⟩

end FX1Poly.Polygraph
