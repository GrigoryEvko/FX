import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TaggedFrontPull
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapSuccessorEnumeration

/-! # TaggedReplay — replay a tag order + the candidate class enumeration (FREE-7)

Iterating the certified pull (`pullTagToFront?`) over a whole tag order REPLAYS it: the
result is a trace equivalent to the input whose tag list is exactly the requested order.
Filtering the replay over every candidate tag order yields the CANDIDATE class
enumeration — the list the unconditional decider (`SaturationFuelBound`) wants.

  * `TaggedReplay` — one certified replay: the reconstructed trace, its `TaggedTraceEquiv`
    certificate, and the tag-order equation, riding in the value;
  * ★ `replayTagOrder?` — pull each requested tag to the front in turn, recursing behind
    it (`consCongr` reassembles the certificates); honestly `none` when a pull fails or
    the lengths mismatch;
  * `consEachTagOnto` / `allTagOrdersOfLength` / `allTagOrdersOfLength_containsOrder` —
    every length-`n` tag order over an alphabet, with membership completeness (any order
    of the right length whose tags live in the alphabet is enumerated; repetition is
    allowed — soundness never needs dup-freedom, and the completeness consumer discharges
    tag membership by the shipped count invariance);
  * `spineTagList_length` / `untagSpineAtoms_length` — the two projections preserve
    length (the bridge from trace length to tag-order length);
  * ★ `classEnumerationCandidate` / `classEnumerationCandidate_isSound` — the candidate
    enumeration: replay every candidate order against the consecutively-tagged seed and
    untag; SOUNDNESS is unconditional (every member is trace-equivalent to the seed, by
    the replay certificate through the untagging projection).

HONESTY: COMPLETENESS of the candidate enumeration (every trace equivalent to the seed
appears) is exactly the DETERMINATION rung — reachable tagged traces with equal tag
orders are equal — and that rung is FALSE: `TagOrderNonDetermination.lean` mechanizes
the Eckmann–Hilton side-flip witness (`tagOrder_doesNotDetermineClassMember`,
`classEnumerationCandidate_isNotComplete`).  This enumeration therefore stays a SOUND
under-approximation only; the complete class list for
`SaturationFuelBound.decideAtomicTraceEquivOfCompleteClassList` must come from a
bounded-atom-universe argument instead.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The projections preserve length -/

/-- The tag-order projection preserves length. -/
theorem spineTagList_length {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (taggedList : List (TaggedSpineAtom signature sourceMode targetMode)) →
    (spineTagList taggedList).length = taggedList.length
  | [] => rfl
  | _taggedAtom :: rest => congrArg (· + 1) (spineTagList_length rest)

/-- The untagging projection preserves length. -/
theorem untagSpineAtoms_length {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (taggedList : List (TaggedSpineAtom signature sourceMode targetMode)) →
    (untagSpineAtoms taggedList).length = taggedList.length
  | [] => rfl
  | _taggedAtom :: rest => congrArg (· + 1) (untagSpineAtoms_length rest)

/-! ## The certified replay -/

/-- **One certified replay**: the reconstructed trace with its equivalence certificate
and its tag-order equation riding in the value. -/
structure TaggedReplay (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} (tagOrder : List Nat)
    (taggedTrace : List (TaggedSpineAtom signature overallSource overallTarget)) where
  /-- The trace reconstructed in the requested order. -/
  replayedTrace : List (TaggedSpineAtom signature overallSource overallTarget)
  /-- The replay is a chain of certified adjacent swaps. -/
  isEquivalent : TaggedTraceEquiv signature taggedTrace replayedTrace
  /-- The reconstruction fires in exactly the requested order. -/
  hasTagOrder : spineTagList replayedTrace = tagOrder

/-- ★ **The computable replay**: pull each requested tag to the front in turn and recurse
behind it — `consCongr` lifts the tail's certificate past the pulled head, `trans` chains
it onto the pull's own certificate.  `none` when a pull fails (absent tag or dependent
crossing) or the order and the trace disagree in length. -/
def replayTagOrder? {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode} :
    (tagOrder : List Nat) →
    (taggedTrace : List (TaggedSpineAtom signature overallSource overallTarget)) →
    Option (TaggedReplay signature tagOrder taggedTrace)
  | [], [] => some ⟨[], TaggedTraceEquiv.refl [], rfl⟩
  | [], _taggedHead :: _taggedRest => none
  | nextTag :: restOrder, taggedTrace =>
      match pullTagToFront? modeDecEq modalityDecEq nextTag taggedTrace with
      | none => none
      | some pull =>
          match replayTagOrder? modeDecEq modalityDecEq restOrder pull.pulledRest with
          | none => none
          | some tailReplay =>
              some ⟨pull.pulledHead :: tailReplay.replayedTrace,
                TaggedTraceEquiv.trans pull.isEquivalent
                  (TaggedTraceEquiv.consCongr pull.pulledHead tailReplay.isEquivalent),
                by
                  dsimp only [spineTagList]
                  rw [pull.hasTargetTag, tailReplay.hasTagOrder]⟩

/-! ## Every candidate tag order, enumerated -/

/-- For each alphabet tag, cons it onto every suffix; concatenate the per-tag blocks. -/
def consEachTagOnto : List Nat → List (List Nat) → List (List Nat)
  | [], _suffixes => []
  | tag :: restAlphabet, suffixes =>
      suffixes.map (fun suffix => tag :: suffix) ++ consEachTagOnto restAlphabet suffixes

/-- All tag orders of the given length over an alphabet (repetition allowed — soundness
never needs dup-freedom, and completeness only needs coverage). -/
def allTagOrdersOfLength : Nat → List Nat → List (List Nat)
  | 0, _alphabet => [[]]
  | lengthBudget + 1, alphabet =>
      consEachTagOnto alphabet (allTagOrdersOfLength lengthBudget alphabet)

/-- A cons lands in the block of its head tag. -/
theorem consEachTagOnto_containsCons {tag : Nat} {suffix : List Nat}
    {alphabet : List Nat} {suffixes : List (List Nat)}
    (tagMem : tag ∈ alphabet) (suffixMem : suffix ∈ suffixes) :
    tag :: suffix ∈ consEachTagOnto alphabet suffixes := by
  induction tagMem with
  | head restAlphabet =>
      exact listMemAppendOfLeft _ (listMemMapOfMem suffixMem)
  | tail headTag _innerMem innerHypothesis =>
      exact listMemAppendOfRight _ innerHypothesis

/-- ★ **Enumeration completeness**: every tag order whose tags live in the alphabet is
enumerated at its own length. -/
theorem allTagOrdersOfLength_containsOrder :
    (tagOrder : List Nat) → (alphabet : List Nat) →
    (∀ tag, tag ∈ tagOrder → tag ∈ alphabet) →
    tagOrder ∈ allTagOrdersOfLength tagOrder.length alphabet
  | [], _alphabet, _tagsCovered => List.Mem.head []
  | headTag :: restOrder, alphabet, tagsCovered =>
      consEachTagOnto_containsCons (tagsCovered headTag (List.Mem.head restOrder))
        (allTagOrdersOfLength_containsOrder restOrder alphabet
          (fun tag tagMem => tagsCovered tag (List.Mem.tail headTag tagMem)))

/-! ## The candidate class enumeration + its unconditional soundness half -/

/-- ★ **The candidate class enumeration**: tag the seed consecutively, replay every
candidate tag order, untag the successes.  Completeness (every trace equivalent to the
seed appears) awaits the determination rung; soundness below is unconditional. -/
def classEnumerationCandidate {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    (seedAtoms : List (SpineAtom signature overallSource overallTarget)) :
    List (List (SpineAtom signature overallSource overallTarget)) :=
  (allTagOrdersOfLength seedAtoms.length
      (spineTagList (tagSpineAtomsFrom 0 seedAtoms))).filterMap
    (fun tagOrder =>
      Option.map (fun replay => untagSpineAtoms replay.replayedTrace)
        (replayTagOrder? modeDecEq modalityDecEq tagOrder
          (tagSpineAtomsFrom 0 seedAtoms)))

/-- ★ **Candidate soundness**: every enumerated candidate is trace-equivalent to the
seed — the replay certificate, pushed through the untagging projection, with the seed
tagging round-trip erasing the tags on the left. -/
theorem classEnumerationCandidate_isSound {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    {seedAtoms member : List (SpineAtom signature overallSource overallTarget)}
    (memberMem : member ∈ classEnumerationCandidate modeDecEq modalityDecEq seedAtoms) :
    AtomicTraceEquiv signature seedAtoms member := by
  obtain ⟨tagOrder, _orderMem, mapsToMember⟩ := listMemFilterMapInverted memberMem
  cases replayRuns : replayTagOrder? modeDecEq modalityDecEq tagOrder
      (tagSpineAtomsFrom 0 seedAtoms) with
  | none =>
      rw [replayRuns] at mapsToMember
      exact (nomatch mapsToMember)
  | some replay =>
      rw [replayRuns] at mapsToMember
      have untagEq : untagSpineAtoms replay.replayedTrace = member := by
        injection mapsToMember
      have untaggedEquiv := replay.isEquivalent.untagged
      rw [untagSpineAtoms_tagSpineAtomsFrom seedAtoms 0, untagEq] at untaggedEquiv
      exact untaggedEquiv

end FX1Poly.Polygraph
