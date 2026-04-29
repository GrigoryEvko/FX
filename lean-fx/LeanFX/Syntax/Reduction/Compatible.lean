import LeanFX.Syntax.Reduction.ParCompatible

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

theorem StepStar.rename_compatible
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType} :
    StepStar beforeTerm afterTerm →
      StepStar (Term.rename termRenaming beforeTerm)
        (Term.rename termRenaming afterTerm) := by
  intro multiStep
  induction multiStep generalizing targetScope targetCtx with
  | refl term => exact StepStar.refl _
  | step singleStep remainingSteps remainingIH =>
      exact StepStar.step
        (Step.rename_compatible termRenaming singleStep)
        (remainingIH termRenaming)

theorem StepStar.subst_compatible
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceCtx targetCtx typeSubstitution)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType} :
    StepStar beforeTerm afterTerm →
      StepStar (Term.subst termSubstitution beforeTerm)
        (Term.subst termSubstitution afterTerm) := by
  intro multiStep
  induction multiStep generalizing targetScope targetCtx with
  | refl term => exact StepStar.refl _
  | step singleStep remainingSteps remainingIH =>
      exact StepStar.step
        (Step.subst_compatible termSubstitution singleStep)
        (remainingIH termSubstitution)

theorem Conv.rename_compatible
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType} :
    Conv beforeTerm afterTerm →
      Conv (Term.rename termRenaming beforeTerm)
        (Term.rename termRenaming afterTerm) := by
  intro conversionProof
  induction conversionProof generalizing targetScope targetCtx with
  | refl term => exact Conv.refl _
  | sym equivalence equivalenceIH =>
      exact Conv.sym (equivalenceIH termRenaming)
  | trans leftEquivalence rightEquivalence leftIH rightIH =>
      exact Conv.trans (leftIH termRenaming) (rightIH termRenaming)
  | fromStep singleStep =>
      exact Conv.fromStep (Step.rename_compatible termRenaming singleStep)

theorem Conv.subst_compatible
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceCtx targetCtx typeSubstitution)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType} :
    Conv beforeTerm afterTerm →
      Conv (Term.subst termSubstitution beforeTerm)
        (Term.subst termSubstitution afterTerm) := by
  intro conversionProof
  induction conversionProof generalizing targetScope targetCtx with
  | refl term => exact Conv.refl _
  | sym equivalence equivalenceIH =>
      exact Conv.sym (equivalenceIH termSubstitution)
  | trans leftEquivalence rightEquivalence leftIH rightIH =>
      exact Conv.trans (leftIH termSubstitution) (rightIH termSubstitution)
  | fromStep singleStep =>
      exact Conv.fromStep (Step.subst_compatible termSubstitution singleStep)

end LeanFX.Syntax
