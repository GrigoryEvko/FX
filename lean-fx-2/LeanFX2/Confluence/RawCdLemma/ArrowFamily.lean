import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename.Main
import LeanFX2.Reduction.RawParCompatible.Substitution
import LeanFX2.Reduction.RawParWeakenInv

/-! # LeanFX2.Confluence.RawCdLemma.ArrowFamily

Per-arm helpers for the arrow / path-application families inside
`RawStep.par.cd_lemma`: `lam`, `app`, `betaApp`, `betaAppDeep`,
`pathLamCong`, `pathAppCong`, `betaPathApp`, `betaPathAppDeep`,
`betaPathReflApp`.

Each helper extracts the proof body of one inductive arm in the
headline `RawStep.par.cd_lemma`; the dispatcher in
`Confluence/RawCdLemma.lean` calls these helpers with the
inductive hypotheses produced by `induction ... with`.

Splitting the original 927-LoC `RawCdLemma.lean` along ctor-family
boundaries lets `lake -j` parallelize compilation of each helper.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCdLemma`
dispatcher. -/

namespace LeanFX2

/-- `lam` cong arm. -/
theorem RawStep.par.cd_lemma_lam {scope : Nat}
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    (bodyIH : RawStep.par bodyRawTarget (RawTerm.cd bodyRawSource)) :
    RawStep.par (RawTerm.lam bodyRawTarget)
      (RawTerm.cd (RawTerm.lam bodyRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.lam bodyIH

/-- `app` cong arm with redex split. -/
theorem RawStep.par.cd_lemma_app {scope : Nat}
    {functionRawSource functionRawTarget
     argumentRawSource argumentRawTarget : RawTerm scope}
    (functionIH :
      RawStep.par functionRawTarget (RawTerm.cd functionRawSource))
    (argumentIH :
      RawStep.par argumentRawTarget (RawTerm.cd argumentRawSource)) :
    RawStep.par (RawTerm.app functionRawTarget argumentRawTarget)
      (RawTerm.cd (RawTerm.app functionRawSource argumentRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdAppCase]
  split
  case _ body cdFunctionEq =>
      exact RawStep.par.betaAppDeep
        (cdFunctionEq ▸ functionIH) argumentIH
  all_goals exact RawStep.par.app functionIH argumentIH

/-- Shallow β-redex on app. -/
theorem RawStep.par.cd_lemma_betaApp {scope : Nat}
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {argumentRawSource argumentRawTarget : RawTerm scope}
    (bodyIH : RawStep.par bodyRawTarget (RawTerm.cd bodyRawSource))
    (argumentIH :
      RawStep.par argumentRawTarget (RawTerm.cd argumentRawSource)) :
    RawStep.par (bodyRawTarget.subst0 argumentRawTarget)
      (RawTerm.cd (RawTerm.app (RawTerm.lam bodyRawSource)
                                argumentRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.subst0_par bodyIH argumentIH

/-- Deep β-redex on app: function develops to a `lam`. -/
theorem RawStep.par.cd_lemma_betaAppDeep {scope : Nat}
    {functionRawSource : RawTerm scope}
    {bodyRawTarget : RawTerm (scope + 1)}
    {argumentRawSource argumentRawTarget : RawTerm scope}
    (functionIH :
      RawStep.par (RawTerm.lam bodyRawTarget) (RawTerm.cd functionRawSource))
    (argumentIH :
      RawStep.par argumentRawTarget (RawTerm.cd argumentRawSource)) :
    RawStep.par (bodyRawTarget.subst0 argumentRawTarget)
      (RawTerm.cd (RawTerm.app functionRawSource argumentRawSource)) := by
  simp only [RawTerm.cd]
  obtain ⟨bodyAfter, cdFunctionEq, bodyParStep⟩ :=
    RawStep.par.lam_inv functionIH
  rw [cdFunctionEq]
  exact RawStep.par.subst0_par bodyParStep argumentIH

/-- `pathLam` cong arm. -/
theorem RawStep.par.cd_lemma_pathLamCong {scope : Nat}
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    (bodyIH : RawStep.par bodyRawTarget (RawTerm.cd bodyRawSource)) :
    RawStep.par (RawTerm.pathLam bodyRawTarget)
      (RawTerm.cd (RawTerm.pathLam bodyRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.pathLamCong bodyIH

/-- `pathApp` cong arm with redex split. -/
theorem RawStep.par.cd_lemma_pathAppCong {scope : Nat}
    {pathRawSource pathRawTarget
     intervalRawSource intervalRawTarget : RawTerm scope}
    (pathIH : RawStep.par pathRawTarget (RawTerm.cd pathRawSource))
    (intervalIH :
      RawStep.par intervalRawTarget (RawTerm.cd intervalRawSource)) :
    RawStep.par (RawTerm.pathApp pathRawTarget intervalRawTarget)
      (RawTerm.cd (RawTerm.pathApp pathRawSource intervalRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdPathAppCase]
  split
  case _ bodyRawTarget pathEqn =>
      exact RawStep.par.betaPathAppDeep
        (pathEqn ▸ pathIH) intervalIH
  all_goals exact RawStep.par.pathAppCong pathIH intervalIH

/-- Shallow β-redex on pathApp. -/
theorem RawStep.par.cd_lemma_betaPathApp {scope : Nat}
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {intervalRawSource intervalRawTarget : RawTerm scope}
    (bodyIH : RawStep.par bodyRawTarget (RawTerm.cd bodyRawSource))
    (intervalIH :
      RawStep.par intervalRawTarget (RawTerm.cd intervalRawSource)) :
    RawStep.par (bodyRawTarget.subst0 intervalRawTarget)
      (RawTerm.cd (RawTerm.pathApp (RawTerm.pathLam bodyRawSource)
                                    intervalRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdPathAppCase]
  exact RawStep.par.subst0_par bodyIH intervalIH

/-- Deep β-redex on pathApp: path develops to `pathLam`. -/
theorem RawStep.par.cd_lemma_betaPathAppDeep {scope : Nat}
    {pathRawSource : RawTerm scope}
    {bodyRawTarget : RawTerm (scope + 1)}
    {intervalRawSource intervalRawTarget : RawTerm scope}
    (pathIH :
      RawStep.par (RawTerm.pathLam bodyRawTarget) (RawTerm.cd pathRawSource))
    (intervalIH :
      RawStep.par intervalRawTarget (RawTerm.cd intervalRawSource)) :
    RawStep.par (bodyRawTarget.subst0 intervalRawTarget)
      (RawTerm.cd (RawTerm.pathApp pathRawSource intervalRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdPathAppCase]
  obtain ⟨bodyAfter, cdPathEq, bodyParStep⟩ :=
    RawStep.par.pathLam_inv pathIH
  rw [cdPathEq]
  exact RawStep.par.subst0_par bodyParStep intervalIH

/-- Refl-instantiation β on pathApp. -/
theorem RawStep.par.cd_lemma_betaPathReflApp {scope : Nat}
    {valueRawSource valueRawTarget
     intervalRawSource intervalRawTarget : RawTerm scope}
    (valueIH : RawStep.par valueRawTarget (RawTerm.cd valueRawSource))
    (_intervalIH :
      RawStep.par intervalRawTarget (RawTerm.cd intervalRawSource)) :
    RawStep.par valueRawTarget
      (RawTerm.cd (RawTerm.pathApp
        (RawTerm.pathLam valueRawSource.weaken) intervalRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdPathAppCase, RawTerm.cd_weaken,
             RawTerm.weaken_subst_singleton]
  exact valueIH

end LeanFX2
