import LeanFX2.Reduction.ParRed.ParCasts
import LeanFX2.Term.Subst

/-! # LeanFX2.Reduction.Compat.HoTT.FunextFamily

Typed compositional `rename`/`subst` compat lemmas for the
funext / refl-fragment family of HoTT cong constructors:

* `funextReflCong` — canonical pointwise-refl funext (Pi/Id binder)
* `funextReflAtIdCong` — canonical Id-typed funext at arrow types
* `funextIntroHetCong` — heterogeneous-carrier funext-introduction

Split from `LeanFX2/Reduction/Compat/HoTT.lean` (REFACTOR-COMPAT
#1556) — keeps the parent module under the 1000-line ceiling.

## Root status

Layer 2 reduction-compat HoTT helper.  All declarations remain
zero-axiom under `#print axioms` and preserve their original
fully-qualified namespace `LeanFX2.Step.par.XCong.{rename,subst}_compatible`. -/

namespace LeanFX2

namespace Step

namespace par

/-! ### `funextReflCong` (canonical pointwise-refl funext).

`Term.funextRefl domainType codomainType applyRaw` has Ty
`Ty.piTy domainType (Ty.id codomainType.weaken applyRaw applyRaw)`
and raw form `RawTerm.lam (RawTerm.refl applyRaw)` at scope+1.

The rename arm in `Term/Rename.lean` returns `codomainEqInverse ▸
Term.funextRefl (domainType.rename rho) (codomainType.rename rho)
(applyRaw.rename rho.lift)` where `codomainEqInverse :
(codomainType.rename rho).weaken = codomainType.weaken.rename rho.lift`
is `(Ty.weaken_rename_commute rho codomainType).symm`.

The cast wraps the WHOLE Term (not just an inner subterm).  We bridge
by using the SAME `codomainEqInverse` to transport the
`Step.par.funextReflCong` proof on the un-cast un-renamed-codomain
side to the post-cast Ty index.  Since Step.par is fully heterogeneous
in its source/target Ty, the same `Step.par.funextReflCong` builds
either side; the cast on the proof simply realigns the dependent
contexts. -/
namespace funextReflCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    {applyRawSource applyRawTarget : RawTerm (sourceScope + 1)}
    (renamedApplyRawStep :
      RawStep.par (applyRawSource.rename rho.lift)
                  (applyRawTarget.rename rho.lift)) :
    Step.par
      (Term.rename termRenaming
        (Term.funextRefl (context := sourceCtx)
                         domainType codomainType applyRawSource))
      (Term.rename termRenaming
        (Term.funextRefl (context := sourceCtx)
                         domainType codomainType applyRawTarget)) :=
  by
    simp only [Term.rename]
    exact Step.par.castTargetType
      (funextReflType_rename rho domainType codomainType
        applyRawTarget).symm
      (Step.par.castSourceType
        (funextReflType_rename rho domainType codomainType
          applyRawSource).symm
        (Step.par.funextReflCong (domainType.rename rho)
          (codomainType.rename rho) renamedApplyRawStep))

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (domainType codomainType : Ty level sourceScope)
    {applyRawSource applyRawTarget : RawTerm (sourceScope + 1)}
    (substitutedApplyRawStep :
      RawStep.par (applyRawSource.subst sigma.forRaw.lift)
                  (applyRawTarget.subst sigma.forRaw.lift)) :
    Step.par
      (Term.subst termSubst
        (Term.funextRefl (context := sourceCtx)
                         domainType codomainType applyRawSource))
      (Term.subst termSubst
        (Term.funextRefl (context := sourceCtx)
                         domainType codomainType applyRawTarget)) :=
  by
    simp only [Term.subst]
    exact Step.par.castTargetType
      (funextReflType_subst sigma domainType codomainType
        applyRawTarget).symm
      (Step.par.castSourceType
        (funextReflType_subst sigma domainType codomainType
          applyRawSource).symm
        (Step.par.funextReflCong (domainType.subst sigma)
          (codomainType.subst sigma) substitutedApplyRawStep))

end funextReflCong

/-! ### `funextReflAtIdCong` (canonical Id-typed funext at arrow types).

Mirror of `funextReflCong` at the Id-typed shape: `Term.funextReflAtId
domainType codomainType applyRaw` has Ty
`Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam (RawTerm.refl
applyRaw)) (RawTerm.lam (RawTerm.refl applyRaw))`.  Unlike
`funextReflCong`, no `Ty.weaken_*_commute` cast is needed because
`Ty.id` and `Ty.arrow` are non-binder carriers whose substitution
doesn't introduce a scope shift.  The applyRaw at scope+1 lifts via
`rho.lift` / `sigma.forRaw.lift`. -/
namespace funextReflAtIdCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    {applyRawSource applyRawTarget : RawTerm (sourceScope + 1)}
    (renamedApplyRawStep :
      RawStep.par (applyRawSource.rename rho.lift)
                  (applyRawTarget.rename rho.lift)) :
    Step.par
      (Term.rename termRenaming
        (Term.funextReflAtId (context := sourceCtx)
                             domainType codomainType applyRawSource))
      (Term.rename termRenaming
        (Term.funextReflAtId (context := sourceCtx)
                             domainType codomainType applyRawTarget)) :=
  Step.par.funextReflAtIdCong (domainType.rename rho)
                              (codomainType.rename rho)
                              renamedApplyRawStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (domainType codomainType : Ty level sourceScope)
    {applyRawSource applyRawTarget : RawTerm (sourceScope + 1)}
    (substitutedApplyRawStep :
      RawStep.par (applyRawSource.subst sigma.forRaw.lift)
                  (applyRawTarget.subst sigma.forRaw.lift)) :
    Step.par
      (Term.subst termSubst
        (Term.funextReflAtId (context := sourceCtx)
                             domainType codomainType applyRawSource))
      (Term.subst termSubst
        (Term.funextReflAtId (context := sourceCtx)
                             domainType codomainType applyRawTarget)) :=
  Step.par.funextReflAtIdCong (domainType.subst sigma)
                              (codomainType.subst sigma)
                              substitutedApplyRawStep

end funextReflAtIdCong

/-! ### `funextIntroHetCong` (heterogeneous-carrier funext-introduction).

`Term.funextIntroHet domainType codomainType applyARaw applyBRaw`
has Ty `Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam
applyARaw) (RawTerm.lam applyBRaw)` and raw form `RawTerm.lam
(RawTerm.refl applyARaw)`.  The constructor stores both `applyARaw`
and `applyBRaw` at scope+1; the `Step.par.funextIntroHetCong` rule
takes TWO `RawStep.par` premises (one per applyRaw).  Like
`funextReflAtIdCong`, no `Ty.weaken_*_commute` cast is needed —
`Ty.id` / `Ty.arrow` are non-binder carriers. -/
namespace funextIntroHetCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    {applyARawSource applyARawTarget applyBRawSource applyBRawTarget :
      RawTerm (sourceScope + 1)}
    (renamedApplyARawStep :
      RawStep.par (applyARawSource.rename rho.lift)
                  (applyARawTarget.rename rho.lift))
    (renamedApplyBRawStep :
      RawStep.par (applyBRawSource.rename rho.lift)
                  (applyBRawTarget.rename rho.lift)) :
    Step.par
      (Term.rename termRenaming
        (Term.funextIntroHet (context := sourceCtx)
                             domainType codomainType
                             applyARawSource applyBRawSource))
      (Term.rename termRenaming
        (Term.funextIntroHet (context := sourceCtx)
                             domainType codomainType
                             applyARawTarget applyBRawTarget)) :=
  Step.par.funextIntroHetCong (domainType.rename rho)
                              (codomainType.rename rho)
                              renamedApplyARawStep renamedApplyBRawStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (domainType codomainType : Ty level sourceScope)
    {applyARawSource applyARawTarget applyBRawSource applyBRawTarget :
      RawTerm (sourceScope + 1)}
    (substitutedApplyARawStep :
      RawStep.par (applyARawSource.subst sigma.forRaw.lift)
                  (applyARawTarget.subst sigma.forRaw.lift))
    (substitutedApplyBRawStep :
      RawStep.par (applyBRawSource.subst sigma.forRaw.lift)
                  (applyBRawTarget.subst sigma.forRaw.lift)) :
    Step.par
      (Term.subst termSubst
        (Term.funextIntroHet (context := sourceCtx)
                             domainType codomainType
                             applyARawSource applyBRawSource))
      (Term.subst termSubst
        (Term.funextIntroHet (context := sourceCtx)
                             domainType codomainType
                             applyARawTarget applyBRawTarget)) :=
  Step.par.funextIntroHetCong (domainType.subst sigma)
                              (codomainType.subst sigma)
                              substitutedApplyARawStep
                              substitutedApplyBRawStep

end funextIntroHetCong

end par

end Step

end LeanFX2
