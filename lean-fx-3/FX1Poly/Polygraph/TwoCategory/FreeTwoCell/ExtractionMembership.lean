import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FrontExtraction

/-! # ExtractionMembership — the enumeration's membership kit (FREE-6b)

The exchange argument reasons about MEMBERS of `frontExtractions` in both directions:
exhibiting a matching candidate in one list's enumeration (constructors) and case-analyzing
an arbitrary member of the other's (the destructor).  This file ships that plumbing:

  * hand-rolled zero-axiom `List.Mem` lemmas (`listMemConsCases`, `listMemAppendOfLeft`,
    `listMemAppendOfRight`, `listMemAppendCases`, `listMemFilterMapOfMem`,
    `listMemFilterMapInverted`) — the core `mem_append`/`mem_filterMap` iff lemmas are
    axiom-unaudited, so membership is constructed and inverted by hand;
  * the three enumeration CONSTRUCTORS: `frontExtractions_containsHead`,
    `frontExtractions_containsForwardLift`, `frontExtractions_containsReverseLift` —
    given a tail candidate and a successful recognizer run, the lifted candidate is
    enumerated (stated existentially over the data fields; the certificate is definitional
    by proof irrelevance);
  * the DESTRUCTOR `frontExtractions_memCases`: every enumerated candidate is the head
    extraction, a forward lift, or a reverse lift — with the recognizer run and the tail
    candidate exposed;
  * `frontExtractions_nilHasNoMember` — the empty spine enumerates nothing.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Hand-rolled list membership -/

/-- Membership in a cons is the head or membership in the tail. -/
theorem listMemConsCases {elementType : Type} {element headElement : elementType}
    {tailList : List elementType} (membershipWitness : element ∈ headElement :: tailList) :
    element = headElement ∨ element ∈ tailList := by
  cases membershipWitness with
  | head => exact Or.inl rfl
  | tail _ innerMembership => exact Or.inr innerMembership

/-- Membership in the left half of an append. -/
theorem listMemAppendOfLeft {elementType : Type} {element : elementType}
    {frontList : List elementType} (backList : List elementType)
    (elementMem : element ∈ frontList) : element ∈ frontList ++ backList := by
  induction elementMem with
  | head remaining => exact List.Mem.head (remaining ++ backList)
  | tail headElement _ innerHypothesis => exact List.Mem.tail headElement innerHypothesis

/-- Membership in the right half of an append. -/
theorem listMemAppendOfRight {elementType : Type} {element : elementType}
    {backList : List elementType} :
    (frontList : List elementType) → element ∈ backList → element ∈ frontList ++ backList
  | [], elementMem => elementMem
  | headElement :: remaining, elementMem =>
      List.Mem.tail headElement (listMemAppendOfRight remaining elementMem)

/-- Membership in an append comes from one of the halves. -/
theorem listMemAppendCases {elementType : Type} {element : elementType} :
    (frontList : List elementType) → {backList : List elementType} →
    element ∈ frontList ++ backList → element ∈ frontList ∨ element ∈ backList
  | [], _, splitMem => Or.inr splitMem
  | headElement :: remaining, backList, splitMem => by
      have splitMemReduced : element ∈ headElement :: (remaining ++ backList) := splitMem
      cases splitMemReduced with
      | head => exact Or.inl (List.Mem.head remaining)
      | tail _ innerMembership =>
          cases listMemAppendCases remaining innerMembership with
          | inl inFront => exact Or.inl (List.Mem.tail headElement inFront)
          | inr inBack => exact Or.inr inBack

/-- Membership in a `filterMap`, constructed from a source member with a `some` image. -/
theorem listMemFilterMapOfMem {sourceType targetType : Type}
    {transform : sourceType → Option targetType} {element : sourceType}
    {inputList : List sourceType} (elementMem : element ∈ inputList) {image : targetType}
    (imageEq : transform element = some image) :
    image ∈ inputList.filterMap transform := by
  induction elementMem with
  | head remaining =>
      dsimp only [List.filterMap]
      rw [imageEq]
      exact List.Mem.head (List.filterMap transform remaining)
  | tail headElement _ innerHypothesis =>
      dsimp only [List.filterMap]
      cases headImage : transform headElement with
      | none => exact innerHypothesis
      | some mappedHead => exact List.Mem.tail mappedHead innerHypothesis

/-- Membership in a `filterMap` inverts to a source member with a `some` image. -/
theorem listMemFilterMapInverted {sourceType targetType : Type}
    {transform : sourceType → Option targetType} {image : targetType} :
    {inputList : List sourceType} → image ∈ inputList.filterMap transform →
    ∃ preimage, preimage ∈ inputList ∧ transform preimage = some image
  | [], imageMem => nomatch imageMem
  | headElement :: remaining, imageMem => by
      cases headImage : transform headElement with
      | none =>
          have imageMemReduced : image ∈ List.filterMap transform remaining := by
            dsimp only [List.filterMap] at imageMem
            rw [headImage] at imageMem
            exact imageMem
          obtain ⟨preimage, preimageMem, preimageEq⟩ :=
            listMemFilterMapInverted imageMemReduced
          exact ⟨preimage, List.Mem.tail headElement preimageMem, preimageEq⟩
      | some mappedHead =>
          have imageMemReduced : image ∈ mappedHead :: List.filterMap transform remaining := by
            dsimp only [List.filterMap] at imageMem
            rw [headImage] at imageMem
            exact imageMem
          cases imageMemReduced with
          | head => exact ⟨headElement, List.Mem.head remaining, headImage⟩
          | tail _ innerMembership =>
              obtain ⟨preimage, preimageMem, preimageEq⟩ :=
                listMemFilterMapInverted innerMembership
              exact ⟨preimage, List.Mem.tail headElement preimageMem, preimageEq⟩

/-! ## The enumeration's constructors -/

/-- The head extraction is enumerated. -/
theorem frontExtractions_containsHead {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    (atom : SpineAtom signature overallSource overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    ∃ headExtraction : FrontExtraction (atom :: rest),
      headExtraction ∈ frontExtractions modeDecEq modalityDecEq (atom :: rest)
        ∧ headExtraction.frontAtom = atom ∧ headExtraction.remainder = rest :=
  ⟨⟨atom, rest, AtomicTraceEquiv.refl (atom :: rest)⟩, List.Mem.head _, rfl, rfl⟩

/-- ★ A tail candidate whose front FORWARD-recognizes against the head lifts into the
enumeration: the lifted candidate (front `firstAfterSwap`, the head rejoining the
remainder as `secondAfterSwap`) is enumerated. -/
theorem frontExtractions_containsForwardLift {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    (atom : SpineAtom signature overallSource overallTarget)
    {rest : List (SpineAtom signature overallSource overallTarget)}
    (tailExtraction : FrontExtraction rest)
    (tailMem : tailExtraction ∈ frontExtractions modeDecEq modalityDecEq rest)
    {witness : AdjacentSwapWitness atom tailExtraction.frontAtom}
    (recognized : recognizeAdjacentSwap modeDecEq modalityDecEq atom
      tailExtraction.frontAtom = PSum.inl witness) :
    ∃ lifted : FrontExtraction (atom :: rest),
      lifted ∈ frontExtractions modeDecEq modalityDecEq (atom :: rest)
        ∧ lifted.frontAtom = witness.firstAfterSwap
        ∧ lifted.remainder = witness.secondAfterSwap :: tailExtraction.remainder := by
  have liftedCertificate : AtomicTraceEquiv signature
      (witness.firstAfterSwap :: witness.secondAfterSwap :: tailExtraction.remainder)
      (atom :: rest) :=
    AtomicTraceEquiv.trans
      (AtomicTraceEquiv.symm (AtomicTraceEquiv.ofSwap
        (witness.toSwap tailExtraction.remainder)))
      (AtomicTraceEquiv.consCongr atom tailExtraction.isTraceEquivalent)
  exact ⟨⟨witness.firstAfterSwap,
      witness.secondAfterSwap :: tailExtraction.remainder, liftedCertificate⟩,
    List.Mem.tail _ (listMemAppendOfLeft _
      (listMemFilterMapOfMem tailMem (by rw [recognized]))),
    rfl, rfl⟩

/-- ★ A tail candidate whose front REVERSE-recognizes against the head lifts into the
enumeration: the lifted candidate (front `movedFront`, the head rejoining the remainder
as `stayedBehind`) is enumerated. -/
theorem frontExtractions_containsReverseLift {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    (atom : SpineAtom signature overallSource overallTarget)
    {rest : List (SpineAtom signature overallSource overallTarget)}
    (tailExtraction : FrontExtraction rest)
    (tailMem : tailExtraction ∈ frontExtractions modeDecEq modalityDecEq rest)
    {witness : ReverseAdjacentSwapWitness atom tailExtraction.frontAtom}
    (recognized : recognizeReverseAdjacentSwap modeDecEq modalityDecEq atom
      tailExtraction.frontAtom = PSum.inl witness) :
    ∃ lifted : FrontExtraction (atom :: rest),
      lifted ∈ frontExtractions modeDecEq modalityDecEq (atom :: rest)
        ∧ lifted.frontAtom = witness.movedFront
        ∧ lifted.remainder = witness.stayedBehind :: tailExtraction.remainder := by
  have liftedCertificate : AtomicTraceEquiv signature
      (witness.movedFront :: witness.stayedBehind :: tailExtraction.remainder)
      (atom :: rest) :=
    AtomicTraceEquiv.trans
      (AtomicTraceEquiv.ofSwap (witness.toSwap tailExtraction.remainder))
      (AtomicTraceEquiv.consCongr atom tailExtraction.isTraceEquivalent)
  exact ⟨⟨witness.movedFront,
      witness.stayedBehind :: tailExtraction.remainder, liftedCertificate⟩,
    List.Mem.tail _ (listMemAppendOfRight _
      (listMemFilterMapOfMem tailMem (by rw [recognized]))),
    rfl, rfl⟩

/-! ## The enumeration's destructor -/

/-- The empty spine enumerates nothing. -/
theorem frontExtractions_nilHasNoMember {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    {extraction : FrontExtraction ([] : List (SpineAtom signature overallSource
      overallTarget))}
    (extractionMem : extraction ∈ frontExtractions modeDecEq modalityDecEq []) :
    False :=
  nomatch extractionMem

/-- ★ **The enumeration destructor**: every enumerated candidate of a cons is the head
extraction, a FORWARD lift of an enumerated tail candidate, or a REVERSE lift of one —
with the recognizer run and the tail candidate exposed for downstream surgery. -/
theorem frontExtractions_memCases {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    {atom : SpineAtom signature overallSource overallTarget}
    {rest : List (SpineAtom signature overallSource overallTarget)}
    {extraction : FrontExtraction (atom :: rest)}
    (extractionMem : extraction ∈ frontExtractions modeDecEq modalityDecEq (atom :: rest)) :
    (extraction.frontAtom = atom ∧ extraction.remainder = rest)
      ∨ (∃ tailExtraction : FrontExtraction rest,
          tailExtraction ∈ frontExtractions modeDecEq modalityDecEq rest
            ∧ ∃ witness : AdjacentSwapWitness atom tailExtraction.frontAtom,
              recognizeAdjacentSwap modeDecEq modalityDecEq atom
                  tailExtraction.frontAtom = PSum.inl witness
                ∧ extraction.frontAtom = witness.firstAfterSwap
                ∧ extraction.remainder
                    = witness.secondAfterSwap :: tailExtraction.remainder)
      ∨ (∃ tailExtraction : FrontExtraction rest,
          tailExtraction ∈ frontExtractions modeDecEq modalityDecEq rest
            ∧ ∃ witness : ReverseAdjacentSwapWitness atom tailExtraction.frontAtom,
              recognizeReverseAdjacentSwap modeDecEq modalityDecEq atom
                  tailExtraction.frontAtom = PSum.inl witness
                ∧ extraction.frontAtom = witness.movedFront
                ∧ extraction.remainder
                    = witness.stayedBehind :: tailExtraction.remainder) := by
  rcases listMemConsCases extractionMem with extractionIsHead | extractionInLifts
  · exact Or.inl ⟨congrArg FrontExtraction.frontAtom extractionIsHead,
      congrArg FrontExtraction.remainder extractionIsHead⟩
  · rcases listMemAppendCases _ extractionInLifts with forwardMembership | reverseMembership
    · obtain ⟨tailExtraction, tailMem, liftEq⟩ :=
        listMemFilterMapInverted forwardMembership
      cases recognized : recognizeAdjacentSwap modeDecEq modalityDecEq atom
          tailExtraction.frontAtom with
      | inl witness =>
          rw [recognized] at liftEq
          injection liftEq with liftedEqExtraction
          exact Or.inr (Or.inl ⟨tailExtraction, tailMem, witness, recognized,
            (congrArg FrontExtraction.frontAtom liftedEqExtraction).symm,
            (congrArg FrontExtraction.remainder liftedEqExtraction).symm⟩)
      | inr refuted =>
          rw [recognized] at liftEq
          have noneIsSome : (none : Option (FrontExtraction (atom :: rest)))
              = some extraction := liftEq
          injection noneIsSome
    · obtain ⟨tailExtraction, tailMem, liftEq⟩ :=
        listMemFilterMapInverted reverseMembership
      cases recognized : recognizeReverseAdjacentSwap modeDecEq modalityDecEq atom
          tailExtraction.frontAtom with
      | inl witness =>
          rw [recognized] at liftEq
          injection liftEq with liftedEqExtraction
          exact Or.inr (Or.inr ⟨tailExtraction, tailMem, witness, recognized,
            (congrArg FrontExtraction.frontAtom liftedEqExtraction).symm,
            (congrArg FrontExtraction.remainder liftedEqExtraction).symm⟩)
      | inr refuted =>
          rw [recognized] at liftEq
          have noneIsSome : (none : Option (FrontExtraction (atom :: rest)))
              = some extraction := liftEq
          injection noneIsSome

end FX1Poly.Polygraph
