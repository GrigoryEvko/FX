import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ExtractionMembership
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapInversion

/-! # SwapExtractionTransport — recognizer totality + whole-trace transport (FREE-6b)

The matched-or-beaten exchange lemma's base case: across ONE adjacent swap, the entire
other side of the swap is itself an enumerated front extraction.  This file ships the two
tools and the two transport directions:

  * `recognizeAdjacentSwap_firesOnWitness` / `recognizeReverseAdjacentSwap_firesOnWitness`
    — TOTALITY ON A WITNESS: whenever a swap certificate exists, the recognizer returns
    `PSum.inl` (the negative arm refutes the certificate in hand).  Together with the
    reconstruction-agreement corollaries of `SwapInversion` this pins a recognizer's
    output on any known swap — the exchange lemma's head-swap cases never inspect the
    recognizer's computation;
  * `SpineAtomSwap.targetIsExtractionOfSource` — the swap's RHS, as a whole trace
    (front AND remainder), is enumerated among the LHS's front extractions: the forward
    lift of the tail's head extraction across the constructor's own witness;
  * `SpineAtomSwap.sourceIsExtractionOfTarget` — the mirror: the LHS is enumerated among
    the RHS's front extractions, by the reverse lift.

Consequence for the exchange analysis: the HEAD extraction of either side of a swap is
always MATCHED in the other side's enumeration — with the remainder agreeing on the nose,
not merely up to trace equivalence.  Only the lifted (deeper) extractions can produce the
Eckmann–Hilton phantom fronts that force the matched-or-beaten weakening.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Recognizer totality on a witness -/

/-- The FORWARD recognizer fires whenever a forward certificate exists: the negative arm
would refute the certificate in hand. -/
theorem recognizeAdjacentSwap_firesOnWitness {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    {leftAtom rightAtom : SpineAtom signature overallSource overallTarget}
    (witness : AdjacentSwapWitness leftAtom rightAtom) :
    ∃ returnedWitness : AdjacentSwapWitness leftAtom rightAtom,
      recognizeAdjacentSwap modeDecEq modalityDecEq leftAtom rightAtom
        = PSum.inl returnedWitness := by
  cases recognizerRun : recognizeAdjacentSwap modeDecEq modalityDecEq leftAtom
      rightAtom with
  | inl returnedWitness => exact ⟨returnedWitness, rfl⟩
  | inr refuted => exact (refuted witness).elim

/-- The REVERSE recognizer fires whenever a reverse certificate exists. -/
theorem recognizeReverseAdjacentSwap_firesOnWitness {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    {headAtom movingAtom : SpineAtom signature overallSource overallTarget}
    (witness : ReverseAdjacentSwapWitness headAtom movingAtom) :
    ∃ returnedWitness : ReverseAdjacentSwapWitness headAtom movingAtom,
      recognizeReverseAdjacentSwap modeDecEq modalityDecEq headAtom movingAtom
        = PSum.inl returnedWitness := by
  cases recognizerRun : recognizeReverseAdjacentSwap modeDecEq modalityDecEq headAtom
      movingAtom with
  | inl returnedWitness => exact ⟨returnedWitness, rfl⟩
  | inr refuted => exact (refuted witness).elim

/-! ## Whole-trace transport across one swap -/

/-- ★ **The swap's RHS is an enumerated extraction of its LHS**: forward-invert the swap,
head-extract the LHS's second atom, and lift it forward across the recognizer's witness —
the reconstruction-agreement corollaries convert the recognizer's output into the
constructor's own reconstruction. -/
theorem SpineAtomSwap.targetIsExtractionOfSource {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    {sourceList targetList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature sourceList targetList) :
    ∃ lifted : FrontExtraction sourceList,
      lifted ∈ frontExtractions modeDecEq modalityDecEq sourceList
        ∧ lifted.frontAtom :: lifted.remainder = targetList := by
  obtain ⟨leftAtom, rightAtom, rest, constructorWitness, lhsShape, rhsShape⟩ :=
    swapStep.forwardInversion
  subst lhsShape
  subst rhsShape
  obtain ⟨returnedWitness, recognizerFires⟩ :=
    recognizeAdjacentSwap_firesOnWitness modeDecEq modalityDecEq constructorWitness
  obtain ⟨lifted, liftedMem, liftedFrontEq, liftedRemainderEq⟩ :=
    frontExtractions_containsForwardLift modeDecEq modalityDecEq leftAtom
      ⟨rightAtom, rest, AtomicTraceEquiv.refl (rightAtom :: rest)⟩
      (List.Mem.head _) recognizerFires
  refine ⟨lifted, liftedMem, ?_⟩
  rw [liftedFrontEq, liftedRemainderEq,
    AdjacentSwapWitness.firstAfterSwapCoincides returnedWitness constructorWitness,
    AdjacentSwapWitness.secondAfterSwapCoincides returnedWitness constructorWitness]

/-- ★ **The swap's LHS is an enumerated extraction of its RHS**: the mirror through the
reverse inversion and the reverse lift. -/
theorem SpineAtomSwap.sourceIsExtractionOfTarget {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    {sourceList targetList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature sourceList targetList) :
    ∃ lifted : FrontExtraction targetList,
      lifted ∈ frontExtractions modeDecEq modalityDecEq targetList
        ∧ lifted.frontAtom :: lifted.remainder = sourceList := by
  obtain ⟨headAtom, movingAtom, rest, constructorWitness, rhsShape, lhsShape⟩ :=
    swapStep.reverseInversion
  subst rhsShape
  subst lhsShape
  obtain ⟨returnedWitness, recognizerFires⟩ :=
    recognizeReverseAdjacentSwap_firesOnWitness modeDecEq modalityDecEq
      constructorWitness
  obtain ⟨lifted, liftedMem, liftedFrontEq, liftedRemainderEq⟩ :=
    frontExtractions_containsReverseLift modeDecEq modalityDecEq headAtom
      ⟨movingAtom, rest, AtomicTraceEquiv.refl (movingAtom :: rest)⟩
      (List.Mem.head _) recognizerFires
  refine ⟨lifted, liftedMem, ?_⟩
  rw [liftedFrontEq, liftedRemainderEq,
    ReverseAdjacentSwapWitness.movedFrontCoincides returnedWitness constructorWitness,
    ReverseAdjacentSwapWitness.stayedBehindCoincides returnedWitness constructorWitness]

end FX1Poly.Polygraph
