import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename.Main
import LeanFX2.Reduction.RawPar.Inductive
import LeanFX2.Reduction.RawParInversion.AtomicCtors

/-! # LeanFX2.Confluence.RawCdLemma.BoolNatArms

Per-arm helpers for boolean / nat eliminator arms inside
`RawStep.par.cd_lemma`: `boolElim`, `natSucc`, `natElim`,
`natRec`, plus their shallow + deep ι-redex arms.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCdLemma`
dispatcher. -/

namespace LeanFX2

/-- `boolElim` cong arm with two-redex split. -/
theorem RawStep.par.cd_lemma_boolElim {scope : Nat}
    {scrutineeRawSource scrutineeRawTarget
     thenRawSource thenRawTarget
     elseRawSource elseRawTarget : RawTerm scope}
    (scrutineeIH :
      RawStep.par scrutineeRawTarget (RawTerm.cd scrutineeRawSource))
    (thenIH : RawStep.par thenRawTarget (RawTerm.cd thenRawSource))
    (elseIH : RawStep.par elseRawTarget (RawTerm.cd elseRawSource)) :
    RawStep.par
      (RawTerm.boolElim scrutineeRawTarget thenRawTarget elseRawTarget)
      (RawTerm.cd
        (RawTerm.boolElim scrutineeRawSource thenRawSource elseRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdBoolElimCase]
  split
  case _ cdScrutineeEq =>
      exact RawStep.par.iotaBoolElimTrueDeep _
        (cdScrutineeEq ▸ scrutineeIH) thenIH
  case _ cdScrutineeEq =>
      exact RawStep.par.iotaBoolElimFalseDeep _
        (cdScrutineeEq ▸ scrutineeIH) elseIH
  all_goals exact RawStep.par.boolElim scrutineeIH thenIH elseIH

/-- `natSucc` cong arm. -/
theorem RawStep.par.cd_lemma_natSucc {scope : Nat}
    {predRawSource predRawTarget : RawTerm scope}
    (predIH : RawStep.par predRawTarget (RawTerm.cd predRawSource)) :
    RawStep.par (RawTerm.natSucc predRawTarget)
      (RawTerm.cd (RawTerm.natSucc predRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.natSucc predIH

/-- `natElim` cong arm with zero/succ split. -/
theorem RawStep.par.cd_lemma_natElim {scope : Nat}
    {scrutineeRawSource scrutineeRawTarget
     zeroRawSource zeroRawTarget
     succRawSource succRawTarget : RawTerm scope}
    (scrutineeIH :
      RawStep.par scrutineeRawTarget (RawTerm.cd scrutineeRawSource))
    (zeroIH : RawStep.par zeroRawTarget (RawTerm.cd zeroRawSource))
    (succIH : RawStep.par succRawTarget (RawTerm.cd succRawSource)) :
    RawStep.par
      (RawTerm.natElim scrutineeRawTarget zeroRawTarget succRawTarget)
      (RawTerm.cd
        (RawTerm.natElim scrutineeRawSource zeroRawSource succRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdNatElimCase]
  split
  case _ cdScrutineeEq =>
      exact RawStep.par.iotaNatElimZeroDeep _
        (cdScrutineeEq ▸ scrutineeIH) zeroIH
  case _ pred cdScrutineeEq =>
      exact RawStep.par.iotaNatElimSuccDeep _
        (cdScrutineeEq ▸ scrutineeIH) succIH
  all_goals exact RawStep.par.natElim scrutineeIH zeroIH succIH

/-- `natRec` cong arm with zero/succ split. -/
theorem RawStep.par.cd_lemma_natRec {scope : Nat}
    {scrutineeRawSource scrutineeRawTarget
     zeroRawSource zeroRawTarget
     succRawSource succRawTarget : RawTerm scope}
    (scrutineeIH :
      RawStep.par scrutineeRawTarget (RawTerm.cd scrutineeRawSource))
    (zeroIH : RawStep.par zeroRawTarget (RawTerm.cd zeroRawSource))
    (succIH : RawStep.par succRawTarget (RawTerm.cd succRawSource)) :
    RawStep.par
      (RawTerm.natRec scrutineeRawTarget zeroRawTarget succRawTarget)
      (RawTerm.cd
        (RawTerm.natRec scrutineeRawSource zeroRawSource succRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdNatRecCase]
  split
  case _ cdScrutineeEq =>
      exact RawStep.par.iotaNatRecZeroDeep _
        (cdScrutineeEq ▸ scrutineeIH) zeroIH
  case _ pred cdScrutineeEq =>
      exact RawStep.par.iotaNatRecSuccDeep
        (cdScrutineeEq ▸ scrutineeIH) zeroIH succIH
  all_goals exact RawStep.par.natRec scrutineeIH zeroIH succIH

/-- Shallow ι: bool-elim on `true`. -/
theorem RawStep.par.cd_lemma_iotaBoolElimTrue {scope : Nat}
    {thenRawSource thenRawTarget : RawTerm scope}
    (elseBranch : RawTerm scope)
    (thenIH : RawStep.par thenRawTarget (RawTerm.cd thenRawSource)) :
    RawStep.par thenRawTarget
      (RawTerm.cd (RawTerm.boolElim RawTerm.boolTrue
        thenRawSource elseBranch)) := by
  simp only [RawTerm.cd]
  exact thenIH

/-- Shallow ι: bool-elim on `false`. -/
theorem RawStep.par.cd_lemma_iotaBoolElimFalse {scope : Nat}
    {elseRawSource elseRawTarget : RawTerm scope}
    (thenBranch : RawTerm scope)
    (elseIH : RawStep.par elseRawTarget (RawTerm.cd elseRawSource)) :
    RawStep.par elseRawTarget
      (RawTerm.cd (RawTerm.boolElim RawTerm.boolFalse
        thenBranch elseRawSource)) := by
  simp only [RawTerm.cd]
  exact elseIH

/-- Shallow ι: nat-elim on `natZero`. -/
theorem RawStep.par.cd_lemma_iotaNatElimZero {scope : Nat}
    {zeroRawSource zeroRawTarget : RawTerm scope}
    (succBranch : RawTerm scope)
    (zeroIH : RawStep.par zeroRawTarget (RawTerm.cd zeroRawSource)) :
    RawStep.par zeroRawTarget
      (RawTerm.cd (RawTerm.natElim RawTerm.natZero
        zeroRawSource succBranch)) := by
  simp only [RawTerm.cd]
  exact zeroIH

/-- Shallow ι: nat-elim on `natSucc`. -/
theorem RawStep.par.cd_lemma_iotaNatElimSucc {scope : Nat}
    {predRawSource predRawTarget
     succRawSource succRawTarget : RawTerm scope}
    (zeroBranch : RawTerm scope)
    (predIH : RawStep.par predRawTarget (RawTerm.cd predRawSource))
    (succIH : RawStep.par succRawTarget (RawTerm.cd succRawSource)) :
    RawStep.par (RawTerm.app succRawTarget predRawTarget)
      (RawTerm.cd (RawTerm.natElim (RawTerm.natSucc predRawSource)
        zeroBranch succRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.app succIH predIH

/-- Shallow ι: nat-rec on `natZero`. -/
theorem RawStep.par.cd_lemma_iotaNatRecZero {scope : Nat}
    {zeroRawSource zeroRawTarget : RawTerm scope}
    (succBranch : RawTerm scope)
    (zeroIH : RawStep.par zeroRawTarget (RawTerm.cd zeroRawSource)) :
    RawStep.par zeroRawTarget
      (RawTerm.cd (RawTerm.natRec RawTerm.natZero
        zeroRawSource succBranch)) := by
  simp only [RawTerm.cd]
  exact zeroIH

/-- Shallow ι: nat-rec on `natSucc`. -/
theorem RawStep.par.cd_lemma_iotaNatRecSucc {scope : Nat}
    {predRawSource predRawTarget
     zeroRawSource zeroRawTarget
     succRawSource succRawTarget : RawTerm scope}
    (predIH : RawStep.par predRawTarget (RawTerm.cd predRawSource))
    (zeroIH : RawStep.par zeroRawTarget (RawTerm.cd zeroRawSource))
    (succIH : RawStep.par succRawTarget (RawTerm.cd succRawSource)) :
    RawStep.par
      (RawTerm.app (RawTerm.app succRawTarget predRawTarget)
        (RawTerm.natRec predRawTarget zeroRawTarget succRawTarget))
      (RawTerm.cd (RawTerm.natRec (RawTerm.natSucc predRawSource)
        zeroRawSource succRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.app
    (RawStep.par.app succIH predIH)
    (RawStep.par.natRec predIH zeroIH succIH)

/-- Deep ι: bool-elim scrutinee develops to `boolTrue`. -/
theorem RawStep.par.cd_lemma_iotaBoolElimTrueDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {thenRawSource thenRawTarget : RawTerm scope}
    (elseBranch : RawTerm scope)
    (scrutineeIH :
      RawStep.par RawTerm.boolTrue (RawTerm.cd scrutineeRawSource))
    (thenIH : RawStep.par thenRawTarget (RawTerm.cd thenRawSource)) :
    RawStep.par thenRawTarget
      (RawTerm.cd (RawTerm.boolElim scrutineeRawSource
        thenRawSource elseBranch)) := by
  simp only [RawTerm.cd]
  have cdScrutinee := RawStep.par.boolTrue_inv scrutineeIH
  rw [cdScrutinee]
  exact thenIH

/-- Deep ι: bool-elim scrutinee develops to `boolFalse`. -/
theorem RawStep.par.cd_lemma_iotaBoolElimFalseDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {elseRawSource elseRawTarget : RawTerm scope}
    (thenBranch : RawTerm scope)
    (scrutineeIH :
      RawStep.par RawTerm.boolFalse (RawTerm.cd scrutineeRawSource))
    (elseIH : RawStep.par elseRawTarget (RawTerm.cd elseRawSource)) :
    RawStep.par elseRawTarget
      (RawTerm.cd (RawTerm.boolElim scrutineeRawSource
        thenBranch elseRawSource)) := by
  simp only [RawTerm.cd]
  have cdScrutinee := RawStep.par.boolFalse_inv scrutineeIH
  rw [cdScrutinee]
  exact elseIH

/-- Deep ι: nat-elim scrutinee develops to `natZero`. -/
theorem RawStep.par.cd_lemma_iotaNatElimZeroDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {zeroRawSource zeroRawTarget : RawTerm scope}
    (succBranch : RawTerm scope)
    (scrutineeIH :
      RawStep.par RawTerm.natZero (RawTerm.cd scrutineeRawSource))
    (zeroIH : RawStep.par zeroRawTarget (RawTerm.cd zeroRawSource)) :
    RawStep.par zeroRawTarget
      (RawTerm.cd (RawTerm.natElim scrutineeRawSource
        zeroRawSource succBranch)) := by
  simp only [RawTerm.cd]
  have cdScrutinee := RawStep.par.natZero_inv scrutineeIH
  rw [cdScrutinee]
  exact zeroIH

/-- Deep ι: nat-elim scrutinee develops to `natSucc`. -/
theorem RawStep.par.cd_lemma_iotaNatElimSuccDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {predRawTarget : RawTerm scope}
    {succRawSource succRawTarget : RawTerm scope}
    (zeroBranch : RawTerm scope)
    (scrutineeIH :
      RawStep.par (RawTerm.natSucc predRawTarget)
        (RawTerm.cd scrutineeRawSource))
    (succIH : RawStep.par succRawTarget (RawTerm.cd succRawSource)) :
    RawStep.par (RawTerm.app succRawTarget predRawTarget)
      (RawTerm.cd (RawTerm.natElim scrutineeRawSource
        zeroBranch succRawSource)) := by
  simp only [RawTerm.cd]
  obtain ⟨predAfter, cdScrutineeEq, predParStep⟩ :=
    RawStep.par.natSucc_inv scrutineeIH
  rw [cdScrutineeEq]
  exact RawStep.par.app succIH predParStep

/-- Deep ι: nat-rec scrutinee develops to `natZero`. -/
theorem RawStep.par.cd_lemma_iotaNatRecZeroDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {zeroRawSource zeroRawTarget : RawTerm scope}
    (succBranch : RawTerm scope)
    (scrutineeIH :
      RawStep.par RawTerm.natZero (RawTerm.cd scrutineeRawSource))
    (zeroIH : RawStep.par zeroRawTarget (RawTerm.cd zeroRawSource)) :
    RawStep.par zeroRawTarget
      (RawTerm.cd (RawTerm.natRec scrutineeRawSource
        zeroRawSource succBranch)) := by
  simp only [RawTerm.cd]
  have cdScrutinee := RawStep.par.natZero_inv scrutineeIH
  rw [cdScrutinee]
  exact zeroIH

/-- Deep ι: nat-rec scrutinee develops to `natSucc`. -/
theorem RawStep.par.cd_lemma_iotaNatRecSuccDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {predRawTarget : RawTerm scope}
    {zeroRawSource zeroRawTarget
     succRawSource succRawTarget : RawTerm scope}
    (scrutineeIH :
      RawStep.par (RawTerm.natSucc predRawTarget)
        (RawTerm.cd scrutineeRawSource))
    (zeroIH : RawStep.par zeroRawTarget (RawTerm.cd zeroRawSource))
    (succIH : RawStep.par succRawTarget (RawTerm.cd succRawSource)) :
    RawStep.par
      (RawTerm.app (RawTerm.app succRawTarget predRawTarget)
        (RawTerm.natRec predRawTarget zeroRawTarget succRawTarget))
      (RawTerm.cd (RawTerm.natRec scrutineeRawSource
        zeroRawSource succRawSource)) := by
  simp only [RawTerm.cd]
  obtain ⟨predAfter, cdScrutineeEq, predParStep⟩ :=
    RawStep.par.natSucc_inv scrutineeIH
  rw [cdScrutineeEq]
  exact RawStep.par.app
    (RawStep.par.app succIH predParStep)
    (RawStep.par.natRec predParStep zeroIH succIH)

end LeanFX2
