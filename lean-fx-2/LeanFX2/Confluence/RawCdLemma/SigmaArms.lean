import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename.Main
import LeanFX2.Reduction.RawPar.Inductive
import LeanFX2.Reduction.RawParWeakenInv

/-! # LeanFX2.Confluence.RawCdLemma.SigmaArms

Per-arm helpers for Σ-introduction / projection arms inside
`RawStep.par.cd_lemma`: `pair`, `fst`, `snd`, `betaFstPair`,
`betaSndPair`, `betaFstPairDeep`, `betaSndPairDeep`.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCdLemma`
dispatcher. -/

namespace LeanFX2

/-- `pair` cong arm. -/
theorem RawStep.par.cd_lemma_pair {scope : Nat}
    {firstRawSource firstRawTarget
     secondRawSource secondRawTarget : RawTerm scope}
    (firstIH : RawStep.par firstRawTarget (RawTerm.cd firstRawSource))
    (secondIH :
      RawStep.par secondRawTarget (RawTerm.cd secondRawSource)) :
    RawStep.par (RawTerm.pair firstRawTarget secondRawTarget)
      (RawTerm.cd (RawTerm.pair firstRawSource secondRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.pair firstIH secondIH

/-- `fst` cong arm with redex split. -/
theorem RawStep.par.cd_lemma_fst {scope : Nat}
    {pairRawSource pairRawTarget : RawTerm scope}
    (pairIH : RawStep.par pairRawTarget (RawTerm.cd pairRawSource)) :
    RawStep.par (RawTerm.fst pairRawTarget)
      (RawTerm.cd (RawTerm.fst pairRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdFstCase]
  split
  case _ firstVal secondVal cdPairEq =>
      exact RawStep.par.betaFstPairDeep (cdPairEq ▸ pairIH)
  all_goals exact RawStep.par.fst pairIH

/-- `snd` cong arm with redex split. -/
theorem RawStep.par.cd_lemma_snd {scope : Nat}
    {pairRawSource pairRawTarget : RawTerm scope}
    (pairIH : RawStep.par pairRawTarget (RawTerm.cd pairRawSource)) :
    RawStep.par (RawTerm.snd pairRawTarget)
      (RawTerm.cd (RawTerm.snd pairRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdSndCase]
  split
  case _ firstVal secondVal cdPairEq =>
      exact RawStep.par.betaSndPairDeep (cdPairEq ▸ pairIH)
  all_goals exact RawStep.par.snd pairIH

/-- Shallow β-fst on a `pair`. -/
theorem RawStep.par.cd_lemma_betaFstPair {scope : Nat}
    {firstRawSource firstRawTarget : RawTerm scope}
    (secondVal : RawTerm scope)
    (firstIH : RawStep.par firstRawTarget (RawTerm.cd firstRawSource)) :
    RawStep.par firstRawTarget
      (RawTerm.cd (RawTerm.fst (RawTerm.pair firstRawSource secondVal))) := by
  simp only [RawTerm.cd]
  exact firstIH

/-- Shallow β-snd on a `pair`. -/
theorem RawStep.par.cd_lemma_betaSndPair {scope : Nat}
    {secondRawSource secondRawTarget : RawTerm scope}
    (firstVal : RawTerm scope)
    (secondIH :
      RawStep.par secondRawTarget (RawTerm.cd secondRawSource)) :
    RawStep.par secondRawTarget
      (RawTerm.cd (RawTerm.snd (RawTerm.pair firstVal secondRawSource))) := by
  simp only [RawTerm.cd]
  exact secondIH

/-- Deep β-fst: pair develops in cd. -/
theorem RawStep.par.cd_lemma_betaFstPairDeep {scope : Nat}
    {pairRawSource : RawTerm scope}
    {firstAfter secondAfter : RawTerm scope}
    (pairIH :
      RawStep.par (RawTerm.pair firstAfter secondAfter)
        (RawTerm.cd pairRawSource)) :
    RawStep.par firstAfter (RawTerm.cd (RawTerm.fst pairRawSource)) := by
  simp only [RawTerm.cd]
  obtain ⟨firstAfter', secondAfter', cdPairEq, firstParStep, _⟩ :=
    RawStep.par.pair_inv pairIH
  rw [cdPairEq]
  exact firstParStep

/-- Deep β-snd: pair develops in cd. -/
theorem RawStep.par.cd_lemma_betaSndPairDeep {scope : Nat}
    {pairRawSource : RawTerm scope}
    {firstAfter secondAfter : RawTerm scope}
    (pairIH :
      RawStep.par (RawTerm.pair firstAfter secondAfter)
        (RawTerm.cd pairRawSource)) :
    RawStep.par secondAfter (RawTerm.cd (RawTerm.snd pairRawSource)) := by
  simp only [RawTerm.cd]
  obtain ⟨firstAfter', secondAfter', cdPairEq, _, secondParStep⟩ :=
    RawStep.par.pair_inv pairIH
  rw [cdPairEq]
  exact secondParStep

end LeanFX2
