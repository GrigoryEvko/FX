import LeanFX2.Foundation.RawPartialRename.TranspPiContractum
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParRename

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

end LeanFX2
