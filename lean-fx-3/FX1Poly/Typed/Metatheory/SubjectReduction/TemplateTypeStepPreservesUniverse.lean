import FX1Poly.Typed.Metatheory.SubjectReduction.TemplateStepStarUnderChildStep
import FX1Poly.Typed.Metatheory.SubjectReduction.DataEliminatorBranchTypeFormedUnderMotiveStep

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/TemplateTypeStepPreservesUniverse
    — SR-DSL-2 ★ CAPSTONE: the generic type-SR over `CellTemplate` (one lemma, every eliminator)

`templateTypeStepPreservesUniverse` marries the two halves of SR-DSL-2:

  * `templateStepStarUnderChildStep` (the DIRECTED congruence — pure reduction theory): when a cell's children /
    type-index params step pointwise, the `interpret?`-produced classifier REDUCES to the post-step term;
  * `UnionClassifierIsType.preservedUnderStepStar` (universe rigidity — type-level SR): a well-formed type that
    reduces stays a well-formed type.

Their composite: from "the PRE-step branch classifier is a well-formed type" + "the cell's children step
pointwise", produce "the DRIFTED branch classifier is the `interpret?` of the stepped children AND is still a
well-formed type."  This is exactly what SR-DSL-4's `premisesHoldAfter` consumes once per obligation — the drifted
classifier's formedness comes by SR-transfer from the PRE-step classifier (which `classifierIsType` supplies for
the pre-step obligation — NOT circular: the post-step classifier's formedness is never assumed).

ONE lemma covers ALL data eliminators (option / either / list / nat / idJ / bool / any future row): the branch
classifier is a `CellTemplate`, so this generic statement subsumes the per-eliminator `*_formedUnderMotiveStep`
corpus with ZERO per-row work.  The universe-rigidity route also means NO flag coherence, NO threaded flag, NO
`SourceUniverseFlagUnique`, NO descriptor hardening — the whole branch-type formedness transfers across the
directed reduction, never re-forming a `piTyCode` from its legs.

## Zero-axiom

A single `obtain` + `exact` over the two shipped zero-axiom keystones.  No `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, or `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- **★ SR-DSL-2 capstone — generic type-SR over the `CellTemplate` DSL.**  Given a branch / obligation classifier
that `interpret?` builds from a cell's `argsBefore` / `paramsBefore` and that is a well-formed union type, when the
children step pointwise (`StepStarChildren` — the congruence-SR situation: one child of the subject steps, the
rest are `StepStar.refl`), the classifier built from the stepped `argsAfter` / `paramsAfter` exists AND is still a
well-formed union type.

`context` lives at `scope + depth` (the obligation may sit under `depth` binders the template introduces), exactly
where `preservedUnderStepStar` wants it.  `childSubjectReduction` is the single-step-SR self-reference (the
strictly-smaller-derivation IH, discharged at the WF tie-off). -/
theorem templateTypeStepPreservesUniverse {profile : PolyProfile}
    {argShifts paramShifts : List Nat} {scope depth : Nat}
    {argsBefore argsAfter : RawTermChildren argShifts scope}
    {paramsBefore paramsAfter : RawTermChildren paramShifts scope}
    {context : TypingContext profile (scope + depth)}
    (argsStepStar : StepStarChildren argsBefore argsAfter)
    (paramsStepStar : StepStarChildren paramsBefore paramsAfter)
    (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) (flag : UniverseFlag)
    (template : CellTemplate) {classifierBefore : RawTerm (scope + depth)}
    (interpretEq : CellTemplate.interpret? argsBefore paramsBefore levels level0 level1 carrierLevel flag
      depth template = some classifierBefore)
    (formed : UnionClassifierIsType profile context classifierBefore)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    ∃ classifierAfter,
      CellTemplate.interpret? argsAfter paramsAfter levels level0 level1 carrierLevel flag depth template
        = some classifierAfter ∧
      UnionClassifierIsType profile context classifierAfter := by
  obtain ⟨classifierAfter, interpretAfterEq, classifierSteps⟩ :=
    templateStepStarUnderChildStep argsStepStar paramsStepStar levels level0 level1 carrierLevel flag
      depth template classifierBefore interpretEq
  exact ⟨classifierAfter, interpretAfterEq,
    UnionClassifierIsType.preservedUnderStepStar formed classifierSteps childSubjectReduction⟩

end FX1Poly.Typed
