import LeanFX.Syntax.Reduction.ParCompatible

/-! # Multi-step reduction rename / subst compatibility.

`StepStar.rename_compatible` / `subst_compatible` and
`Conv.rename_compatible` / `subst_compatible`: multi-step reduction
and definitional conversion are preserved by both renaming and full
substitution.  Each is a 1-line corollary of the corresponding
`mapStep` lifter (`StepStar.mapStep` / `Conv.mapStep`) applied with
the renaming/substitution as `mapTerm` and the single-step compat
lemma from `Reduction.Rename` / `Reduction.Subst` as `mapSingleStep`.

Stacks atop `Reduction.ParCompatible` (parallel-reduction
versions) so that all four compat lemmas share one transitive
import path. -/

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
    {beforeTerm afterTerm : Term sourceCtx termType}
    (multiStep : StepStar beforeTerm afterTerm) :
    StepStar (Term.rename termRenaming beforeTerm)
             (Term.rename termRenaming afterTerm) :=
  StepStar.mapStep (Term.rename termRenaming)
    (Step.rename_compatible termRenaming) multiStep

theorem StepStar.subst_compatible
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceCtx targetCtx typeSubstitution)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    (multiStep : StepStar beforeTerm afterTerm) :
    StepStar (Term.subst termSubstitution beforeTerm)
             (Term.subst termSubstitution afterTerm) :=
  StepStar.mapStep (Term.subst termSubstitution)
    (Step.subst_compatible termSubstitution) multiStep

theorem Conv.rename_compatible
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    (conversionProof : Conv beforeTerm afterTerm) :
    Conv (Term.rename termRenaming beforeTerm)
         (Term.rename termRenaming afterTerm) :=
  Conv.mapStep (Term.rename termRenaming)
    (Step.rename_compatible termRenaming) conversionProof

theorem Conv.subst_compatible
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceCtx targetCtx typeSubstitution)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    (conversionProof : Conv beforeTerm afterTerm) :
    Conv (Term.subst termSubstitution beforeTerm)
         (Term.subst termSubstitution afterTerm) :=
  Conv.mapStep (Term.subst termSubstitution)
    (Step.subst_compatible termSubstitution) conversionProof

end LeanFX.Syntax
