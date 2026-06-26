import FX1Poly.Typed.Metatheory.SubjectReduction.DataEliminatorBranchTypeFormedUnderMotiveStep
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ObligationReclassifiesUnderDrift
    — SR-DSL-4 atom: re-establish a typing obligation when its subject AND classifier drift

The generic `premisesHoldAfter` (SR-DSL-4) walks an eliminator / intro / formation rule's obligation list under a
child step and re-establishes every obligation at the stepped children.  Each obligation
`HasTypeUnion context subject classifier` faces TWO drifts when one of the cell's children steps:

  * its SUBJECT may step (when the subject IS the stepping child, or a re-based copy of it) — `StepStar
    subjectBefore subjectAfter`;
  * its CLASSIFIER may drift (when the classifier reads the stepping child — the motive case) — `StepStar
    classifierBefore classifierAfter`.

This file ships the ATOM that absorbs both: `obligationReclassifiesUnderDrift` takes the obligation-at-before
typing, the two `StepStar` drifts, and the single-step-SR self-reference, and produces the obligation-at-after
typing.  It is deliberately decoupled from the `CellTemplate` machinery — the directed-congruence engine
(SR-DSL-2's `templateStepStarUnderChildStep`) is what PRODUCES the `classifierDrift` `StepStar`, and the
projection / re-basing structure is what produces the `subjectDrift`; this atom only CONSUMES the two drifts.

The proof is two shipped keystones bolted together:

  1. **Subject SR along the chain** (`subjectReductionAlongChainAtFixedClassifier`) — iterate the single-step-SR
     self-reference along `subjectDrift`, reclassifying each reduct back to the FIXED pre-step classifier (so the
     classifier stays put while the subject walks its whole reduction chain).
  2. **Classifier formedness transfer** (SR-DSL-2's `preservedUnderStepStar`) — the post-step classifier is still
     a well-formed type, so the final `reclassifyToType` from the pre- to the post-step classifier (along the
     `StepStar`-induced `Conv`) is valid.

## Zero-axiom

`StepStar` induction + `reclassifyToType` (the `conv` arm) + the two audited zero-axiom keystones.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Subject reduction along a whole reduction CHAIN at a FIXED classifier.**  Iterating the single-step-SR
self-reference along `StepStar subjectBefore subjectAfter`: each head step re-types the reduct at a `Conv`-equal
classifier, which universe-formedness-of-the-fixed-classifier reclassifies straight back to the SAME classifier,
so the invariant "typed at `classifier`" is maintained the length of the chain.  The classifier never moves — only
the subject walks. -/
theorem subjectReductionAlongChainAtFixedClassifier {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (classifierFormed : UnionClassifierIsType profile context classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    {subjectBefore subjectAfter : RawTerm scope}
    (chain : StepStar subjectBefore subjectAfter) :
    HasTypeUnion profile context subjectBefore classifier →
    HasTypeUnion profile context subjectAfter classifier := by
  induction chain with
  | refl _ => exact id
  | trans headStep _ tailReclassifies =>
      intro holds
      obtain ⟨reductType, reductTyped, convClassifier⟩ := childSubjectReduction holds headStep
      exact tailReclassifies
        (HasTypeUnion.reclassifyToType reductTyped convClassifier.sym classifierFormed)

/-- **★ SR-DSL-4 atom — an obligation reclassifies under subject + classifier drift.**  When one child of an
eliminator / intro / formation cell steps, an obligation `subject : classifier` faces both a subject reduction
(`subjectDrift`) and a classifier reduction (`classifierDrift`).  Given the obligation held before the step and its
classifier was a well-formed type, the obligation holds after: walk the subject to `subjectAfter` at the fixed
pre-step classifier, transfer the classifier's formedness across `classifierDrift` (universe rigidity), then
reclassify from the pre- to the post-step classifier along the `StepStar`-induced `Conv`. -/
theorem obligationReclassifiesUnderDrift {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subjectBefore subjectAfter classifierBefore classifierAfter : RawTerm scope}
    (holds : HasTypeUnion profile context subjectBefore classifierBefore)
    (classifierFormedBefore : UnionClassifierIsType profile context classifierBefore)
    (subjectDrift : StepStar subjectBefore subjectAfter)
    (classifierDrift : StepStar classifierBefore classifierAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    HasTypeUnion profile context subjectAfter classifierAfter := by
  have subjectAfterTyped : HasTypeUnion profile context subjectAfter classifierBefore :=
    subjectReductionAlongChainAtFixedClassifier classifierFormedBefore childSubjectReduction subjectDrift holds
  have classifierFormedAfter : UnionClassifierIsType profile context classifierAfter :=
    UnionClassifierIsType.preservedUnderStepStar classifierFormedBefore classifierDrift childSubjectReduction
  exact HasTypeUnion.reclassifyToType subjectAfterTyped
    ⟨classifierAfter, classifierDrift, StepStar.refl classifierAfter⟩ classifierFormedAfter

end FX1Poly.Typed
