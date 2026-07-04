import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapExtractionTransport
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapChain

/-! # SwapSuccessorEnumeration — the saturation search's move layer (FREE-6c)

The class-saturation route (post-falsification) decides `AtomicTraceEquiv` by bounded
reachability over `OneAdjacentSwap` moves.  This file ships the computable move layer:

  * `swapSuccessors` — enumerate every trace one adjacent swap away, at every position
    and in BOTH directions (the forward recognizer fires `here`, the reverse recognizer
    fires `hereReversed`, the tail recursion under a cons fires `deeper`);
  * `swapSuccessors_isSound` — every enumerated successor is one adjacent swap away
    (the recognizers' certificates ride in their values);
  * `swapSuccessors_isComplete` — ★ every `OneAdjacentSwap` lands in the enumeration:
    the inversions expose the swap's pair and witness, recognizer totality
    (`SwapExtractionTransport`) fires the match arm, and the reconstruction-agreement
    corollaries convert the recognizer's output into the swap's own reconstruction.

Together: `swapSuccessors` computes EXACTLY the `OneAdjacentSwap` neighbors — and
`OneAdjacentSwapChain` (= `AtomicTraceEquiv`, `SwapChain.lean`) is its reflexive-
transitive closure, so the ~-class is exactly what the BFS over this move list reaches.

Also ships the two hand-rolled `List.map` membership lemmas the deeper case needs
(`listMemMapOfMem` / `listMemMapInverted`), continuing the `ExtractionMembership` kit.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Map membership -/

/-- Membership in a `map`, constructed from a source member. -/
theorem listMemMapOfMem {sourceType targetType : Type}
    {transform : sourceType → targetType} {element : sourceType}
    {inputList : List sourceType} (elementMem : element ∈ inputList) :
    transform element ∈ inputList.map transform := by
  induction elementMem with
  | head remaining => exact List.Mem.head _
  | tail headElement _ innerHypothesis => exact List.Mem.tail _ innerHypothesis

/-- Membership in a `map` inverts to a source member. -/
theorem listMemMapInverted {sourceType targetType : Type}
    {transform : sourceType → targetType} {image : targetType} :
    {inputList : List sourceType} → image ∈ inputList.map transform →
    ∃ preimage, preimage ∈ inputList ∧ transform preimage = image
  | [], imageMem => nomatch imageMem
  | headElement :: remaining, imageMem => by
      have imageMemReduced : image ∈ transform headElement :: remaining.map transform :=
        imageMem
      cases imageMemReduced with
      | head => exact ⟨headElement, List.Mem.head remaining, rfl⟩
      | tail _ innerMembership =>
          obtain ⟨preimage, preimageMem, preimageEq⟩ := listMemMapInverted innerMembership
          exact ⟨preimage, List.Mem.tail headElement preimageMem, preimageEq⟩

/-! ## The move enumeration -/

/-- ★ **Enumerate every trace one adjacent swap away**: at the head, the forward
recognizer moves the pair along the constructor direction and the reverse recognizer
against it; deeper positions recurse under the untouched head. -/
def swapSuccessors {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode} :
    List (SpineAtom signature overallSource overallTarget) →
    List (List (SpineAtom signature overallSource overallTarget))
  | [] => []
  | [_lastAtom] => []
  | firstAtom :: secondAtom :: rest =>
      (match recognizeAdjacentSwap modeDecEq modalityDecEq firstAtom secondAtom with
        | PSum.inl witness =>
            [witness.firstAfterSwap :: witness.secondAfterSwap :: rest]
        | PSum.inr _ => []) ++
      ((match recognizeReverseAdjacentSwap modeDecEq modalityDecEq firstAtom
            secondAtom with
        | PSum.inl witness => [witness.movedFront :: witness.stayedBehind :: rest]
        | PSum.inr _ => []) ++
        (swapSuccessors modeDecEq modalityDecEq (secondAtom :: rest)).map
          (fun deeperTrace => firstAtom :: deeperTrace))

/-! ## Soundness -/

/-- Every enumerated successor is one adjacent swap away: the recognizers' witnesses
certify the head arms, the map component recurses. -/
theorem swapSuccessors_isSound {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    {successor : List (SpineAtom signature overallSource overallTarget)} :
    (trace : List (SpineAtom signature overallSource overallTarget)) →
    successor ∈ swapSuccessors modeDecEq modalityDecEq trace →
    OneAdjacentSwap signature trace successor
  | [], successorMem => nomatch successorMem
  | [_lastAtom], successorMem => nomatch successorMem
  | firstAtom :: secondAtom :: rest, successorMem => by
      have successorMemReduced : successor
          ∈ (match recognizeAdjacentSwap modeDecEq modalityDecEq firstAtom
                secondAtom with
              | PSum.inl witness =>
                  [witness.firstAfterSwap :: witness.secondAfterSwap :: rest]
              | PSum.inr _ => []) ++
            ((match recognizeReverseAdjacentSwap modeDecEq modalityDecEq firstAtom
                  secondAtom with
              | PSum.inl witness => [witness.movedFront :: witness.stayedBehind :: rest]
              | PSum.inr _ => []) ++
              (swapSuccessors modeDecEq modalityDecEq (secondAtom :: rest)).map
                (fun deeperTrace => firstAtom :: deeperTrace)) := successorMem
      rcases listMemAppendCases _ successorMemReduced with forwardMem | reverseOrDeeperMem
      · cases recognized : recognizeAdjacentSwap modeDecEq modalityDecEq firstAtom
            secondAtom with
        | inl witness =>
            rw [recognized] at forwardMem
            rcases listMemConsCases forwardMem with successorIsSwapped | impossibleMem
            · rw [successorIsSwapped]
              exact OneAdjacentSwap.here (witness.toSwap rest)
            · exact (nomatch impossibleMem)
        | inr _refuted =>
            rw [recognized] at forwardMem
            exact (nomatch forwardMem)
      · rcases listMemAppendCases _ reverseOrDeeperMem with reverseMem | deeperMem
        · cases recognized : recognizeReverseAdjacentSwap modeDecEq modalityDecEq
              firstAtom secondAtom with
          | inl witness =>
              rw [recognized] at reverseMem
              rcases listMemConsCases reverseMem with successorIsSwapped | impossibleMem
              · rw [successorIsSwapped]
                exact OneAdjacentSwap.hereReversed (witness.toSwap rest)
              · exact (nomatch impossibleMem)
          | inr _refuted =>
              rw [recognized] at reverseMem
              exact (nomatch reverseMem)
        · obtain ⟨deeperTrace, deeperTraceMem, mapEq⟩ := listMemMapInverted deeperMem
          rw [← mapEq]
          exact OneAdjacentSwap.deeper firstAtom
            (swapSuccessors_isSound modeDecEq modalityDecEq (secondAtom :: rest)
              deeperTraceMem)

/-! ## Completeness -/

/-- ★ **Every adjacent swap lands in the enumeration**: the inversions expose the pair
and its witness, recognizer totality fires the arm, and the reconstruction-agreement
corollaries pin the enumerated candidate to the swap's own reconstruction. -/
theorem swapSuccessors_isComplete {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    {trace successor : List (SpineAtom signature overallSource overallTarget)}
    (oneSwap : OneAdjacentSwap signature trace successor) :
    successor ∈ swapSuccessors modeDecEq modalityDecEq trace := by
  induction oneSwap with
  | here swapStep =>
      obtain ⟨leftAtom, rightAtom, restList, constructorWitness, lhsShape, rhsShape⟩ :=
        swapStep.forwardInversion
      subst lhsShape
      subst rhsShape
      obtain ⟨returnedWitness, recognizerFires⟩ :=
        recognizeAdjacentSwap_firesOnWitness modeDecEq modalityDecEq constructorWitness
      have forwardComponentContains : constructorWitness.firstAfterSwap ::
          constructorWitness.secondAfterSwap :: restList
          ∈ (match recognizeAdjacentSwap modeDecEq modalityDecEq leftAtom rightAtom with
              | PSum.inl recognizedWitness =>
                  [recognizedWitness.firstAfterSwap ::
                    recognizedWitness.secondAfterSwap :: restList]
              | PSum.inr _ => []) := by
        rw [recognizerFires,
          AdjacentSwapWitness.firstAfterSwapCoincides constructorWitness returnedWitness,
          AdjacentSwapWitness.secondAfterSwapCoincides constructorWitness
            returnedWitness]
        exact List.Mem.head _
      exact listMemAppendOfLeft _ forwardComponentContains
  | hereReversed swapStep =>
      obtain ⟨headAtom, movingAtom, restList, constructorWitness, rhsShape, lhsShape⟩ :=
        swapStep.reverseInversion
      subst rhsShape
      subst lhsShape
      obtain ⟨returnedWitness, recognizerFires⟩ :=
        recognizeReverseAdjacentSwap_firesOnWitness modeDecEq modalityDecEq
          constructorWitness
      have reverseComponentContains : constructorWitness.movedFront ::
          constructorWitness.stayedBehind :: restList
          ∈ (match recognizeReverseAdjacentSwap modeDecEq modalityDecEq headAtom
                movingAtom with
              | PSum.inl recognizedWitness =>
                  [recognizedWitness.movedFront ::
                    recognizedWitness.stayedBehind :: restList]
              | PSum.inr _ => []) := by
        rw [recognizerFires,
          ReverseAdjacentSwapWitness.movedFrontCoincides constructorWitness
            returnedWitness,
          ReverseAdjacentSwapWitness.stayedBehindCoincides constructorWitness
            returnedWitness]
        exact List.Mem.head _
      exact listMemAppendOfRight _ (listMemAppendOfLeft _ reverseComponentContains)
  | @deeper atom innerFirst innerSecond _innerSwap innerHypothesis =>
      cases innerFirst with
      | nil => exact (nomatch innerHypothesis)
      | cons innerHead innerRest =>
          exact listMemAppendOfRight _ (listMemAppendOfRight _
            (listMemMapOfMem innerHypothesis))

end FX1Poly.Polygraph
