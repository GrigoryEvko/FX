import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParWeakenInv

/-! # LeanFX2.Confluence.RawCdLemma.ModalAndRefine

Per-arm helpers for modal and refinement-type arms inside
`RawStep.par.cd_lemma`: `modIntro`, `modElim`, `betaModElimIntro`,
`betaModElimIntroDeep`, `subsume`, `refineIntroCong`,
`betaRefineElimIntro`, `betaRefineElimIntroDeep`, `refineElimCong`.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCdLemma`
dispatcher. -/

namespace LeanFX2

/-- `modIntro` cong arm. -/
theorem RawStep.par.cd_lemma_modIntro {scope : Nat}
    {innerRawSource innerRawTarget : RawTerm scope}
    (innerIH : RawStep.par innerRawTarget (RawTerm.cd innerRawSource)) :
    RawStep.par (RawTerm.modIntro innerRawTarget)
      (RawTerm.cd (RawTerm.modIntro innerRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.modIntro innerIH

/-- `modElim` cong arm with redex split. -/
theorem RawStep.par.cd_lemma_modElim {scope : Nat}
    {innerRawSource innerRawTarget : RawTerm scope}
    (innerIH : RawStep.par innerRawTarget (RawTerm.cd innerRawSource)) :
    RawStep.par (RawTerm.modElim innerRawTarget)
      (RawTerm.cd (RawTerm.modElim innerRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdModElimCase]
  split
  case _ payloadTarget innerEqn =>
      exact RawStep.par.betaModElimIntroDeep
        (innerEqn ▸ innerIH)
  all_goals exact RawStep.par.modElim innerIH

/-- Shallow β: `modElim (modIntro inner)` contracts. -/
theorem RawStep.par.cd_lemma_betaModElimIntro {scope : Nat}
    {innerRawSource innerRawTarget : RawTerm scope}
    (innerIH : RawStep.par innerRawTarget (RawTerm.cd innerRawSource)) :
    RawStep.par innerRawTarget
      (RawTerm.cd (RawTerm.modElim (RawTerm.modIntro innerRawSource))) := by
  simp only [RawTerm.cd, RawTerm.cdModElimCase]
  exact innerIH

/-- Deep β: inner term develops to `modIntro`. -/
theorem RawStep.par.cd_lemma_betaModElimIntroDeep {scope : Nat}
    {innerRawSource : RawTerm scope}
    {payloadAfter : RawTerm scope}
    (innerIH :
      RawStep.par (RawTerm.modIntro payloadAfter)
        (RawTerm.cd innerRawSource)) :
    RawStep.par payloadAfter
      (RawTerm.cd (RawTerm.modElim innerRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdModElimCase]
  obtain ⟨payloadAfter', cdInnerEq, payloadParStep⟩ :=
    RawStep.par.modIntro_inv innerIH
  rw [cdInnerEq]
  exact payloadParStep

/-- `subsume` cong arm. -/
theorem RawStep.par.cd_lemma_subsume {scope : Nat}
    {innerRawSource innerRawTarget : RawTerm scope}
    (innerIH : RawStep.par innerRawTarget (RawTerm.cd innerRawSource)) :
    RawStep.par (RawTerm.subsume innerRawTarget)
      (RawTerm.cd (RawTerm.subsume innerRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.subsume innerIH

/-- `refineIntroCong` arm. -/
theorem RawStep.par.cd_lemma_refineIntroCong {scope : Nat}
    {valueRawSource valueRawTarget
     proofRawSource proofRawTarget : RawTerm scope}
    (valueIH : RawStep.par valueRawTarget (RawTerm.cd valueRawSource))
    (proofIH : RawStep.par proofRawTarget (RawTerm.cd proofRawSource)) :
    RawStep.par (RawTerm.refineIntro valueRawTarget proofRawTarget)
      (RawTerm.cd (RawTerm.refineIntro valueRawSource proofRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.refineIntroCong valueIH proofIH

/-- Shallow β: `refineElim (refineIntro value proof)` contracts to value. -/
theorem RawStep.par.cd_lemma_betaRefineElimIntro {scope : Nat}
    {valueRawSource valueRawTarget : RawTerm scope}
    {proofRawSource proofRawTarget : RawTerm scope}
    (valueIH : RawStep.par valueRawTarget (RawTerm.cd valueRawSource))
    (proofIH : RawStep.par proofRawTarget (RawTerm.cd proofRawSource)) :
    RawStep.par valueRawTarget
      (RawTerm.cd (RawTerm.refineElim
        (RawTerm.refineIntro valueRawSource proofRawSource))) := by
  simp only [RawTerm.cd, RawTerm.cdRefineElimCase]
  exact valueIH

/-- Deep β: refined term develops to `refineIntro`. -/
theorem RawStep.par.cd_lemma_betaRefineElimIntroDeep {scope : Nat}
    {refinedRawSource : RawTerm scope}
    {valueAfter proofAfter : RawTerm scope}
    (refinedIH :
      RawStep.par (RawTerm.refineIntro valueAfter proofAfter)
        (RawTerm.cd refinedRawSource)) :
    RawStep.par valueAfter
      (RawTerm.cd (RawTerm.refineElim refinedRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdRefineElimCase]
  obtain ⟨valueAfter', proofAfter', cdRefinedEq, valueParStep, _⟩ :=
    RawStep.par.refineIntro_inv refinedIH
  rw [cdRefinedEq]
  exact valueParStep

/-- `refineElimCong` arm with redex split. -/
theorem RawStep.par.cd_lemma_refineElimCong {scope : Nat}
    {refinedRawSource refinedRawTarget : RawTerm scope}
    (refinedIH :
      RawStep.par refinedRawTarget (RawTerm.cd refinedRawSource)) :
    RawStep.par (RawTerm.refineElim refinedRawTarget)
      (RawTerm.cd (RawTerm.refineElim refinedRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdRefineElimCase]
  split
  case _ valueRawTarget proofRawTarget refinedEqn =>
      exact RawStep.par.betaRefineElimIntroDeep
        (refinedEqn ▸ refinedIH)
  all_goals exact RawStep.par.refineElimCong refinedIH

end LeanFX2
