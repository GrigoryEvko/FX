import LeanFX2.Reduction.RawParCompatible.Substitution
import LeanFX2.Reduction.RawParRename

/-! # Reduction/RawParCompatible/NamedCompatibility

Stable compatibility names for raw parallel reduction.

The proofs are thin aliases over the raw rename and substitution
headlines, but keeping these names in a raw leaf lets audit and
bridge consumers avoid importing the typed compatibility umbrella.
-/

namespace LeanFX2

namespace RawStep

namespace par

/-- Compatibility name for raw parallel reduction under renaming. -/
theorem rename_compatible {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    {beforeTerm afterTerm : RawTerm sourceScope}
    (parallelStep : RawStep.par beforeTerm afterTerm) :
    RawStep.par (beforeTerm.rename rawRenaming)
                (afterTerm.rename rawRenaming) :=
  RawStep.par.rename rawRenaming parallelStep

/-- Canonical-weaken specialization of `rename_compatible`.

Surface form `beforeTerm.weaken` / `afterTerm.weaken` matches the
shape downstream β-redex consumers (transp / hcomp cascades, Phase G
β-η critical pair) reach for at call sites.  `RawTerm.weaken`
definitionally unfolds to `RawTerm.rename RawRenaming.weaken`. -/
theorem weaken_compatible {scope : Nat}
    {beforeTerm afterTerm : RawTerm scope}
    (parallelStep : RawStep.par beforeTerm afterTerm) :
    RawStep.par beforeTerm.weaken afterTerm.weaken :=
  RawStep.par.rename_compatible RawRenaming.weaken parallelStep

/-- Compatibility name for raw parallel reduction under related substitutions. -/
theorem subst_compatible {sourceScope targetScope : Nat}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : forall position,
      RawStep.par (firstSubst position) (secondSubst position))
    {beforeTerm afterTerm : RawTerm sourceScope}
    (parallelStep : RawStep.par beforeTerm afterTerm) :
    RawStep.par (beforeTerm.subst firstSubst)
                (afterTerm.subst secondSubst) :=
  RawStep.par.subst_par substsRelated parallelStep

/-- Same-substitution corollary of `subst_compatible`. -/
theorem subst_compatible_same {sourceScope targetScope : Nat}
    (rawSubst : RawTermSubst sourceScope targetScope)
    {beforeTerm afterTerm : RawTerm sourceScope}
    (parallelStep : RawStep.par beforeTerm afterTerm) :
    RawStep.par (beforeTerm.subst rawSubst)
                (afterTerm.subst rawSubst) :=
  RawStep.par.subst_compatible
    (fun position => RawStep.par.refl (rawSubst position))
    parallelStep

/-- Singleton-substitution specialization of `subst_compatible_same`.

Surface form `body.subst0 arg` matches the β-redex shape downstream
K12.28 Geuvers 1992 critical-pair joinability and K13 NbE β-step
consumers reach for: reducing the body of a singleton β-redex while
the argument stays fixed.

`RawTerm.subst0 body arg` is `@[reducible]` defined as
`body.subst (RawTermSubst.singleton arg)`
(`Foundation/RawSubst/SubstDefs.lean:200`), so this is a direct
call to `subst_compatible_same`. -/
theorem subst0_compatible_same {scope : Nat}
    (argTerm : RawTerm scope)
    {beforeBody afterBody : RawTerm (scope + 1)}
    (parallelStep : RawStep.par beforeBody afterBody) :
    RawStep.par (beforeBody.subst0 argTerm)
                (afterBody.subst0 argTerm) :=
  RawStep.par.subst_compatible_same
    (RawTermSubst.singleton argTerm) parallelStep

end par

end RawStep

end LeanFX2
