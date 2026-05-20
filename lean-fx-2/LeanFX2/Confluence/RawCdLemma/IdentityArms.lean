import LeanFX2.Confluence.RawCd.Core
import LeanFX2.Confluence.RawCdRename.Main
import LeanFX2.Reduction.RawPar.Inductive
import LeanFX2.Reduction.RawParInversion.AtomicCtors
import LeanFX2.Reduction.RawParInversion.CubicalAndIdentity

/-! # LeanFX2.Confluence.RawCdLemma.IdentityArms

Per-arm helpers for identity-type, funext-cong, oeq-cong, and
strict-identity arms inside `RawStep.par.cd_lemma`: `reflCong`,
`funextRefl*Cong`, `funextIntroHetCong`, `idJ`, `iotaIdJRefl`,
`iotaIdJReflDeep`, `iotaIdStrictRecRefl`, `iotaIdStrictRecReflDeep`,
`oeqReflCong`, `oeqJCong`, `oeqFunextCong`, `idStrictReflCong`,
`idStrictRecCong`.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCdLemma`
dispatcher. -/

namespace LeanFX2

/-- `reflCong` arm. -/
theorem RawStep.par.cd_lemma_reflCong {scope : Nat}
    {rawTermSource rawTermTarget : RawTerm scope}
    (rawTermIH :
      RawStep.par rawTermTarget (RawTerm.cd rawTermSource)) :
    RawStep.par (RawTerm.refl rawTermTarget)
      (RawTerm.cd (RawTerm.refl rawTermSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.reflCong rawTermIH

/-- `funextReflCong` arm — IH lives at scope + 1. -/
theorem RawStep.par.cd_lemma_funextReflCong {scope : Nat}
    {applyRawSource applyRawTarget : RawTerm (scope + 1)}
    (applyIH : RawStep.par applyRawTarget (RawTerm.cd applyRawSource)) :
    RawStep.par (RawTerm.lam (RawTerm.refl applyRawTarget))
      (RawTerm.cd (RawTerm.lam (RawTerm.refl applyRawSource))) := by
  simp only [RawTerm.cd]
  exact RawStep.par.funextReflCong applyIH

/-- `funextReflAtIdCong` arm — IH lives at scope + 1. -/
theorem RawStep.par.cd_lemma_funextReflAtIdCong {scope : Nat}
    {applyRawSource applyRawTarget : RawTerm (scope + 1)}
    (applyIH : RawStep.par applyRawTarget (RawTerm.cd applyRawSource)) :
    RawStep.par (RawTerm.lam (RawTerm.refl applyRawTarget))
      (RawTerm.cd (RawTerm.lam (RawTerm.refl applyRawSource))) := by
  simp only [RawTerm.cd]
  exact RawStep.par.funextReflAtIdCong applyIH

/-- `funextIntroHetCong` arm — IH lives at scope + 1. -/
theorem RawStep.par.cd_lemma_funextIntroHetCong {scope : Nat}
    {applyARawSource applyARawTarget : RawTerm (scope + 1)}
    (applyAIH :
      RawStep.par applyARawTarget (RawTerm.cd applyARawSource)) :
    RawStep.par (RawTerm.lam (RawTerm.refl applyARawTarget))
      (RawTerm.cd (RawTerm.lam (RawTerm.refl applyARawSource))) := by
  simp only [RawTerm.cd]
  exact RawStep.par.funextIntroHetCong applyAIH

/-- `idJ` cong arm with redex split on witness shape. -/
theorem RawStep.par.cd_lemma_idJ {scope : Nat}
    {baseRawSource baseRawTarget
     witnessRawSource witnessRawTarget : RawTerm scope}
    (baseIH : RawStep.par baseRawTarget (RawTerm.cd baseRawSource))
    (witnessIH :
      RawStep.par witnessRawTarget (RawTerm.cd witnessRawSource)) :
    RawStep.par (RawTerm.idJ baseRawTarget witnessRawTarget)
      (RawTerm.cd (RawTerm.idJ baseRawSource witnessRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdIdJCase]
  split
  case _ rawTerm cdWitnessEq =>
      exact RawStep.par.iotaIdJReflDeep
        (cdWitnessEq ▸ witnessIH) baseIH
  all_goals exact RawStep.par.idJ baseIH witnessIH

/-- Shallow ι: idJ on a `refl` witness. -/
theorem RawStep.par.cd_lemma_iotaIdJRefl {scope : Nat}
    {baseRawSource baseRawTarget : RawTerm scope}
    (rawTerm : RawTerm scope)
    (baseIH : RawStep.par baseRawTarget (RawTerm.cd baseRawSource)) :
    RawStep.par baseRawTarget
      (RawTerm.cd (RawTerm.idJ baseRawSource (RawTerm.refl rawTerm))) := by
  simp only [RawTerm.cd]
  exact baseIH

/-- Shallow ι: idStrictRec on a `idStrictRefl` witness. -/
theorem RawStep.par.cd_lemma_iotaIdStrictRecRefl {scope : Nat}
    {baseRawSource baseRawTarget : RawTerm scope}
    (rawTerm : RawTerm scope)
    (baseIH : RawStep.par baseRawTarget (RawTerm.cd baseRawSource)) :
    RawStep.par baseRawTarget
      (RawTerm.cd (RawTerm.idStrictRec baseRawSource
        (RawTerm.idStrictRefl rawTerm))) := by
  simp only [RawTerm.cd, RawTerm.cdIdStrictRecCase]
  exact baseIH

/-- Deep ι: idJ witness develops to `refl`. -/
theorem RawStep.par.cd_lemma_iotaIdJReflDeep {scope : Nat}
    {witnessRawSource : RawTerm scope}
    {witnessAfter : RawTerm scope}
    {baseRawSource baseRawTarget : RawTerm scope}
    (witnessIH :
      RawStep.par (RawTerm.refl witnessAfter)
        (RawTerm.cd witnessRawSource))
    (baseIH : RawStep.par baseRawTarget (RawTerm.cd baseRawSource)) :
    RawStep.par baseRawTarget
      (RawTerm.cd (RawTerm.idJ baseRawSource witnessRawSource)) := by
  simp only [RawTerm.cd]
  obtain ⟨witnessAfter', cdWitnessEq, _⟩ :=
    RawStep.par.refl_inv witnessIH
  rw [cdWitnessEq]
  exact baseIH

/-- Deep ι: idStrictRec witness develops to `idStrictRefl`. -/
theorem RawStep.par.cd_lemma_iotaIdStrictRecReflDeep {scope : Nat}
    {witnessRawSource : RawTerm scope}
    {witnessAfter : RawTerm scope}
    {baseRawSource baseRawTarget : RawTerm scope}
    (witnessIH :
      RawStep.par (RawTerm.idStrictRefl witnessAfter)
        (RawTerm.cd witnessRawSource))
    (baseIH : RawStep.par baseRawTarget (RawTerm.cd baseRawSource)) :
    RawStep.par baseRawTarget
      (RawTerm.cd (RawTerm.idStrictRec baseRawSource witnessRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdIdStrictRecCase]
  obtain ⟨witnessAfter', cdWitnessEq, _⟩ :=
    RawStep.par.idStrictRefl_inv witnessIH
  rw [cdWitnessEq]
  exact baseIH

/-- `oeqReflCong` arm. -/
theorem RawStep.par.cd_lemma_oeqReflCong {scope : Nat}
    {witnessSource witnessTarget : RawTerm scope}
    (witnessIH :
      RawStep.par witnessTarget (RawTerm.cd witnessSource)) :
    RawStep.par (RawTerm.oeqRefl witnessTarget)
      (RawTerm.cd (RawTerm.oeqRefl witnessSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.oeqReflCong witnessIH

/-- `oeqJCong` arm. -/
theorem RawStep.par.cd_lemma_oeqJCong {scope : Nat}
    {baseSource baseTarget witnessSource witnessTarget : RawTerm scope}
    (baseIH : RawStep.par baseTarget (RawTerm.cd baseSource))
    (witnessIH :
      RawStep.par witnessTarget (RawTerm.cd witnessSource)) :
    RawStep.par (RawTerm.oeqJ baseTarget witnessTarget)
      (RawTerm.cd (RawTerm.oeqJ baseSource witnessSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.oeqJCong baseIH witnessIH

/-- `oeqFunextCong` arm. -/
theorem RawStep.par.cd_lemma_oeqFunextCong {scope : Nat}
    {pointwiseSource pointwiseTarget : RawTerm scope}
    (pointwiseIH :
      RawStep.par pointwiseTarget (RawTerm.cd pointwiseSource)) :
    RawStep.par (RawTerm.oeqFunext pointwiseTarget)
      (RawTerm.cd (RawTerm.oeqFunext pointwiseSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.oeqFunextCong pointwiseIH

/-- `idStrictReflCong` arm. -/
theorem RawStep.par.cd_lemma_idStrictReflCong {scope : Nat}
    {witnessSource witnessTarget : RawTerm scope}
    (witnessIH :
      RawStep.par witnessTarget (RawTerm.cd witnessSource)) :
    RawStep.par (RawTerm.idStrictRefl witnessTarget)
      (RawTerm.cd (RawTerm.idStrictRefl witnessSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.idStrictReflCong witnessIH

/-- `idStrictRecCong` arm with redex split. -/
theorem RawStep.par.cd_lemma_idStrictRecCong {scope : Nat}
    {baseSource baseTarget witnessSource witnessTarget : RawTerm scope}
    (baseIH : RawStep.par baseTarget (RawTerm.cd baseSource))
    (witnessIH :
      RawStep.par witnessTarget (RawTerm.cd witnessSource)) :
    RawStep.par (RawTerm.idStrictRec baseTarget witnessTarget)
      (RawTerm.cd (RawTerm.idStrictRec baseSource witnessSource)) := by
  simp only [RawTerm.cd, RawTerm.cdIdStrictRecCase]
  split
  case _ rawTerm cdWitnessEq =>
      exact RawStep.par.iotaIdStrictRecReflDeep
        (cdWitnessEq ▸ witnessIH) baseIH
  all_goals exact RawStep.par.idStrictRecCong baseIH witnessIH

end LeanFX2
