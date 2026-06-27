import FX1Poly.Typed.Metatheory.SubjectReduction.ObligationReclassifiesUnderDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.UnionChildSubjectReductionBounded

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ObligationReclassifiesUnderDriftBounded
    — SR-WF-TIEOFF (intro third): the FUEL-BOUNDED single-step subject-SR atom

`ObligationReclassifiesUnderDrift.lean` ships the universal-child-SR obligation reclassifier
(`obligationReclassifiesUnderDrift`), whose subject keystone `subjectReductionAlongChainAtFixedClassifier` FOLDS the
universal `UnionChildSubjectReduction` along the WHOLE `StepStar` subject chain.  The SR-WF-TIEOFF fuel induction
supplies only the FUEL-BOUNDED `UnionChildSubjectReductionBelow profile cell.size`, so it can re-type a stepping
subject only when that subject is STRICTLY SMALLER than the cell — which holds exactly for the INTRO arm:

  * an introducer obligation's SUBJECT that actually steps is the stepping ARG (a structural child of
    `rule.memberCell scope args`), so its size is `< memberCell.size` — and it steps EXACTLY ONCE (a single child
    step), so the subject drift is a length-1 chain, never a growing multi-step one; AND
  * every introducer obligation's CLASSIFIER is a param / universe-code (`codomainCode`, `typeParam0/1`,
    `universeCodeCell`) that does NOT read the args, so under an arg step the classifier drift is `refl` — no
    classifier-side child-SR fold at all.

So the intro arm only ever feeds child-SR a SINGLE-STEP subject at a size-bounded arg, with a fixed classifier.  This
file ships exactly that atom: `subjectReductionAtFixedClassifierStepBelow` re-types a subject across ONE step at a
FIXED classifier from the fuel-bounded predicate plus the one size bound `subjectBefore.size < bound`.  It is the
bounded analogue of the single-step case of `subjectReductionAlongChainAtFixedClassifier`, and the load-bearing atom
the intro bounded congruence driver consumes in its `cons` arm.

The ELIM arm is DELIBERATELY NOT covered here: its motive-reading branch classifiers (natElim / listElim) drift
MULTI-STEP, and the classifier-formedness transfer folds child-SR along that chain whose intermediates can exceed
`memberCell.size` — the open SR-WF-TIEOFF elim obstruction (a separate, non-fuel argument is required).

## Zero-axiom

The fuel-bounded predicate application + `reclassifyToType` (the `conv` arm).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Single-step subject reduction at a FIXED classifier, from the fuel-bounded predicate.**  When an introducer
obligation's subject steps ONCE `subjectBefore ⟶ subjectAfter` (the stepping arg, a structural child of the cell, so
`subjectBefore.size < bound`) and its classifier is unchanged (the intro `refl`-classifier case), the obligation
re-holds at the SAME classifier — sourced from `UnionChildSubjectReductionBelow profile bound` rather than the
universal `UnionChildSubjectReduction`.  The bounded single-step analogue of
`subjectReductionAlongChainAtFixedClassifier`; the atom the intro bounded congruence driver's `cons` arm consumes. -/
theorem subjectReductionAtFixedClassifierStepBelow {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (classifierFormed : UnionClassifierIsType profile context classifier)
    {bound : Nat} {subjectBefore subjectAfter : RawTerm scope}
    (subjectStep : Step subjectBefore subjectAfter)
    (subjectBelow : subjectBefore.size < bound)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile bound) :
    HasTypeUnion profile context subjectBefore classifier →
    HasTypeUnion profile context subjectAfter classifier := by
  intro holds
  obtain ⟨reductType, reductTyped, convClassifier⟩ := childSubjectReductionBelow subjectBelow holds subjectStep
  exact HasTypeUnion.reclassifyToType reductTyped convClassifier.sym classifierFormed

end FX1Poly.Typed
