import LeanFX2.Foundation.RawPartialRename.TranspPiContractum
import LeanFX2.Foundation.RawPartialRename.TranspPiPathRecognizer
import LeanFX2.Reduction.RawParRename
import LeanFX2.Reduction.RawParInversion.TypeCodes
import LeanFX2.Reduction.RawParWeakenInv.Weaken

/-! # LeanFX2.Reduction.TranspPiContractumPar

Reduction-layer Phase F prep for D2.5.5: parallel-step
congruence over the transpPi β contractum's source argument.

Future Phase G+I cd_lemma transpPiBetaDeep arm needs to discharge
`RawStep.par (contractum codomain sourceTarget) (contractum
codomain X)` from a par-step hypothesis `RawStep.par sourceTarget
X`.  This file ships the underlying congruence lemma so the
cascade arm can call it directly.

## Root status

Layer 2 reduction primitive.  Strict zero-axiom.  Consumed by
future cd_lemma transpPiBeta + transpPiBetaDeep arms (Phase I) and
by RawParCompatible's transpPiBeta arm (Phase H). -/

namespace LeanFX2

/-- Parallel reduction lifts through `transpPiBetaContractum`'s
source argument.  The contractum's surface form is
`lam (transp (pathLam (codomain.swap01)) (app source.weaken
var₀))`; the source position is reached via outer-lam + transp's
source slot + app's function slot + `.weaken`.

Proof: descend the par-step through each constructor via the cong
rules `lam`, `transpCong`, `app`; refl the constant path-body and
the var₀ argument; lift the source-step under `weaken` via
`RawStep.par.rename` with `RawRenaming.weaken`. -/
theorem RawTerm.transpPiBetaContractum_par_cong {scope : Nat}
    (pathCodomain : RawTerm (scope + 2))
    {developedSourceSource developedSourceTarget : RawTerm scope}
    (sourceStep :
      RawStep.par developedSourceSource developedSourceTarget) :
    RawStep.par
      (RawTerm.transpPiBetaContractum pathCodomain
        developedSourceSource)
      (RawTerm.transpPiBetaContractum pathCodomain
        developedSourceTarget) := by
  show RawStep.par
    (RawTerm.lam (
      RawTerm.transp
        (RawTerm.pathLam (pathCodomain.rename RawRenaming.swap01))
        (RawTerm.app developedSourceSource.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
    ))
    (RawTerm.lam (
      RawTerm.transp
        (RawTerm.pathLam (pathCodomain.rename RawRenaming.swap01))
        (RawTerm.app developedSourceTarget.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
    ))
  exact RawStep.par.lam (
    RawStep.par.transpCong
      (RawStep.par.refl _)
      (RawStep.par.app
        (RawStep.par.rename RawRenaming.weaken sourceStep)
        (RawStep.par.refl _)))

/-- Bi-directional parallel-step cong over `transpPiBetaContractum`:
both the path-codomain code AND the developed source argument may
step simultaneously.  Combines `transpPiBetaContractum_par_cong`
(source-only step) with codomain-cong via the underlying transp /
pathLam / rename cong machinery.

The contractum's surface form is
`lam (transp (pathLam (codomainCode.swap01))
            (app source.weaken var₀))`.

Proof: descend the par-step through each constructor:
* `lam` cong on outer binder
* `transpCong` for the inner transp
* `pathLamCong` on `pathCodomain.rename swap01` (codomain step lifted
  via `RawStep.par.rename RawRenaming.swap01`)
* `app` cong on the body application:
  - `rename RawRenaming.weaken` lifts source par-step under weaken
  - `refl` for the var-zero argument.

Consumed by future Phase G+I cd_lemma transpCong arm: when both the
path body's recognizer fires AND the developed source steps, this is
the joint conclusion we need. -/
theorem RawTerm.transpPiBetaContractum_par_bi_cong {scope : Nat}
    {pathCodomainSource pathCodomainTarget : RawTerm (scope + 2)}
    {developedSourceSource developedSourceTarget : RawTerm scope}
    (codomainStep :
      RawStep.par pathCodomainSource pathCodomainTarget)
    (sourceStep :
      RawStep.par developedSourceSource developedSourceTarget) :
    RawStep.par
      (RawTerm.transpPiBetaContractum pathCodomainSource
        developedSourceSource)
      (RawTerm.transpPiBetaContractum pathCodomainTarget
        developedSourceTarget) := by
  show RawStep.par
    (RawTerm.lam (
      RawTerm.transp
        (RawTerm.pathLam (pathCodomainSource.rename RawRenaming.swap01))
        (RawTerm.app developedSourceSource.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
    ))
    (RawTerm.lam (
      RawTerm.transp
        (RawTerm.pathLam (pathCodomainTarget.rename RawRenaming.swap01))
        (RawTerm.app developedSourceTarget.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
    ))
  exact RawStep.par.lam (
    RawStep.par.transpCong
      (RawStep.par.pathLamCong
        (RawStep.par.rename RawRenaming.swap01 codomainStep))
      (RawStep.par.app
        (RawStep.par.rename RawRenaming.weaken sourceStep)
        (RawStep.par.refl _)))

/-- Recognizer-preservation under parallel reduction: when
`matchTranspPiBetaShape? pathBody = some (innerDomain, codomainCode)`
and `RawStep.par pathBody pathBodyTarget`, the recognizer also fires
on `pathBodyTarget` with a par-related codomain witness.

Proof: soundness rewrites `pathBody = piTyCode innerDomain.weaken
codomainCode`; `piTyCode_inv` extracts the par-related target shape
`piTyCode domainTarget codomainCodeTarget`; `weaken_inv` shows the
target domain has the form `innerDomainTarget.weaken` (existence,
no par-step on the inner domain since `weaken_inv` returns only the
image-shape); completeness fires the recognizer on the rebuilt
piTyCode.

Consumed by future Phase G+I cd_lemma transpCong arm: when the
cd-developed `pathLam pathBody` step has the recognizer fire on the
source pathBody, this lemma lifts the recognizer hit through the
par-step to fire the `transpPiBetaDeep` β rule on the cd-target
side.  Companion to `transpPiBetaContractum_par_bi_cong` — that one
discharges the conclusion after the recognizer is shown to fire;
this one extracts the witness saying it fires. -/
theorem RawTerm.matchTranspPiBetaShape?_par_some {scope : Nat}
    {pathBody pathBodyTarget : RawTerm (scope + 1)}
    {innerDomain : RawTerm scope} {codomainCode : RawTerm (scope + 2)}
    (recognizes :
      RawTerm.matchTranspPiBetaShape? pathBody =
        some (innerDomain, codomainCode))
    (parStep : RawStep.par pathBody pathBodyTarget) :
    ∃ (innerDomainTarget : RawTerm scope)
      (codomainCodeTarget : RawTerm (scope + 2)),
      RawTerm.matchTranspPiBetaShape? pathBodyTarget =
        some (innerDomainTarget, codomainCodeTarget) ∧
      RawStep.par codomainCode codomainCodeTarget := by
  have shapeEq :=
    RawTerm.matchTranspPiBetaShape?_imp_piTyCode_weaken
      pathBody innerDomain codomainCode recognizes
  rw [shapeEq] at parStep
  obtain ⟨domainTarget, codomainCodeTarget, targetEq,
          domainStep, codomainStep⟩ :=
    RawStep.par.piTyCode_inv parStep
  obtain ⟨innerDomainTarget, domainTargetEq⟩ :=
    RawStep.par.weaken_inv (sourceTerm := innerDomain) domainStep
  refine ⟨innerDomainTarget, codomainCodeTarget, ?_, codomainStep⟩
  rw [targetEq, domainTargetEq]
  exact RawTerm.matchTranspPiBetaShape?_piTyCode_weaken
          innerDomainTarget codomainCodeTarget

end LeanFX2
