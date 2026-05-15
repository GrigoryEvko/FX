import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParWeakenInv

/-! # LeanFX2.Confluence.RawCdLemma.CubicalAndEquiv

Per-arm helpers for the cubical / Glue / equiv / HoTT-S-cascade
arms inside `RawStep.par.cd_lemma` that are STRAIGHT cong rules:
`intervalOppCong`, `intervalMeetCong`, `intervalJoinCong`,
`glueIntroCong`, `betaGlueElimIntro`, `betaGlueElimIntroDeep`,
`glueElimCong`, `hcompCong`, `equivIntroCong`, `equivAppCong`,
`pathComposeCong`, `oeqTransCong`, `equivComposeCong`,
`uaToEquivCong`.

Heavy HoTT-S-cascade arms that require head-shape dispatch
(`transpCong`, `equivApplyCong`, `idToEquivCong`,
`uaReflEquivApplyDeep`, etc.) stay inline in the headline
dispatcher because their inline `match` on `RawTerm.cd ...` would
trip Lean's match-compiler propext leak if extracted with explicit
binders.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCdLemma`
dispatcher. -/

namespace LeanFX2

/-- `intervalOppCong` arm. -/
theorem RawStep.par.cd_lemma_intervalOppCong {scope : Nat}
    {intervalRawSource intervalRawTarget : RawTerm scope}
    (intervalIH :
      RawStep.par intervalRawTarget (RawTerm.cd intervalRawSource)) :
    RawStep.par (RawTerm.intervalOpp intervalRawTarget)
      (RawTerm.cd (RawTerm.intervalOpp intervalRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.intervalOppCong intervalIH

/-- `intervalMeetCong` arm. -/
theorem RawStep.par.cd_lemma_intervalMeetCong {scope : Nat}
    {leftRawSource leftRawTarget
     rightRawSource rightRawTarget : RawTerm scope}
    (leftIH : RawStep.par leftRawTarget (RawTerm.cd leftRawSource))
    (rightIH : RawStep.par rightRawTarget (RawTerm.cd rightRawSource)) :
    RawStep.par (RawTerm.intervalMeet leftRawTarget rightRawTarget)
      (RawTerm.cd (RawTerm.intervalMeet leftRawSource
        rightRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.intervalMeetCong leftIH rightIH

/-- `intervalJoinCong` arm. -/
theorem RawStep.par.cd_lemma_intervalJoinCong {scope : Nat}
    {leftRawSource leftRawTarget
     rightRawSource rightRawTarget : RawTerm scope}
    (leftIH : RawStep.par leftRawTarget (RawTerm.cd leftRawSource))
    (rightIH : RawStep.par rightRawTarget (RawTerm.cd rightRawSource)) :
    RawStep.par (RawTerm.intervalJoin leftRawTarget rightRawTarget)
      (RawTerm.cd (RawTerm.intervalJoin leftRawSource
        rightRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.intervalJoinCong leftIH rightIH

/-- `glueIntroCong` arm. -/
theorem RawStep.par.cd_lemma_glueIntroCong {scope : Nat}
    {baseRawSource baseRawTarget
     partialRawSource partialRawTarget : RawTerm scope}
    (baseIH : RawStep.par baseRawTarget (RawTerm.cd baseRawSource))
    (partialIH :
      RawStep.par partialRawTarget (RawTerm.cd partialRawSource)) :
    RawStep.par (RawTerm.glueIntro baseRawTarget partialRawTarget)
      (RawTerm.cd (RawTerm.glueIntro baseRawSource
        partialRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.glueIntroCong baseIH partialIH

/-- Shallow β: `glueElim (glueIntro base partial)` contracts to base. -/
theorem RawStep.par.cd_lemma_betaGlueElimIntro {scope : Nat}
    {baseRawSource baseRawTarget
     partialRawSource partialRawTarget : RawTerm scope}
    (baseIH : RawStep.par baseRawTarget (RawTerm.cd baseRawSource))
    (partialIH :
      RawStep.par partialRawTarget (RawTerm.cd partialRawSource)) :
    RawStep.par baseRawTarget
      (RawTerm.cd (RawTerm.glueElim
        (RawTerm.glueIntro baseRawSource partialRawSource))) := by
  simp only [RawTerm.cd, RawTerm.cdGlueElimCase]
  exact baseIH

/-- Deep β: glued term develops to `glueIntro`. -/
theorem RawStep.par.cd_lemma_betaGlueElimIntroDeep {scope : Nat}
    {gluedRawSource : RawTerm scope}
    {baseAfter partialAfter : RawTerm scope}
    (gluedIH :
      RawStep.par (RawTerm.glueIntro baseAfter partialAfter)
        (RawTerm.cd gluedRawSource)) :
    RawStep.par baseAfter
      (RawTerm.cd (RawTerm.glueElim gluedRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdGlueElimCase]
  obtain ⟨baseAfter', partialAfter', cdGluedEq, baseParStep, _⟩ :=
    RawStep.par.glueIntro_inv gluedIH
  rw [cdGluedEq]
  exact baseParStep

/-- `glueElimCong` arm with redex split. -/
theorem RawStep.par.cd_lemma_glueElimCong {scope : Nat}
    {gluedRawSource gluedRawTarget : RawTerm scope}
    (gluedIH :
      RawStep.par gluedRawTarget (RawTerm.cd gluedRawSource)) :
    RawStep.par (RawTerm.glueElim gluedRawTarget)
      (RawTerm.cd (RawTerm.glueElim gluedRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdGlueElimCase]
  split
  case _ baseRawTarget partialRawTarget gluedEqn =>
      exact RawStep.par.betaGlueElimIntroDeep
        (gluedEqn ▸ gluedIH)
  all_goals exact RawStep.par.glueElimCong gluedIH

/-- `hcompCong` arm.

D2.5.2: now dispatches on `cd sidesRawSource`'s shape via
`cdHcompCase`.  When `cd sidesRawSource = pathLam X.weaken`,
fire `hcompBetaDeep`; otherwise fall through to `hcompCong`.  Mirror
of the transpCong arm. -/
theorem RawStep.par.cd_lemma_hcompCong {scope : Nat}
    {sidesRawSource sidesRawTarget
     capRawSource capRawTarget : RawTerm scope}
    (sidesIH : RawStep.par sidesRawTarget (RawTerm.cd sidesRawSource))
    (capIH : RawStep.par capRawTarget (RawTerm.cd capRawSource)) :
    RawStep.par (RawTerm.hcomp sidesRawTarget capRawTarget)
      (RawTerm.cd (RawTerm.hcomp sidesRawSource capRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdHcompCase]
  split
  case _ sidesBody sidesBodyEqn =>
      rw [sidesBodyEqn] at sidesIH
      split
      case _ innerCap unwknEqn =>
          have hSides : sidesBody = innerCap.weaken :=
            RawTerm.unweaken?_imp_weaken sidesBody innerCap unwknEqn
          rw [hSides] at sidesIH
          exact RawStep.par.hcompBetaDeep sidesIH capIH
      case _ _unwknEqn =>
          exact RawStep.par.hcompCong sidesIH capIH
  all_goals exact RawStep.par.hcompCong sidesIH capIH

/-- `equivIntroCong` arm. -/
theorem RawStep.par.cd_lemma_equivIntroCong {scope : Nat}
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm scope}
    (forwardIH :
      RawStep.par forwardRawTarget (RawTerm.cd forwardRawSource))
    (backwardIH :
      RawStep.par backwardRawTarget (RawTerm.cd backwardRawSource)) :
    RawStep.par (RawTerm.equivIntro forwardRawTarget backwardRawTarget)
      (RawTerm.cd (RawTerm.equivIntro forwardRawSource
        backwardRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.equivIntroCong forwardIH backwardIH

/-- `equivAppCong` arm. -/
theorem RawStep.par.cd_lemma_equivAppCong {scope : Nat}
    {equivRawSource equivRawTarget
     argumentRawSource argumentRawTarget : RawTerm scope}
    (equivIH : RawStep.par equivRawTarget (RawTerm.cd equivRawSource))
    (argumentIH :
      RawStep.par argumentRawTarget (RawTerm.cd argumentRawSource)) :
    RawStep.par (RawTerm.equivApp equivRawTarget argumentRawTarget)
      (RawTerm.cd (RawTerm.equivApp equivRawSource
        argumentRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.equivAppCong equivIH argumentIH

/-- `pathComposeCong` arm — D3.6-S3 pure cong. -/
theorem RawStep.par.cd_lemma_pathComposeCong {scope : Nat}
    {leftRawSource leftRawTarget
     rightRawSource rightRawTarget : RawTerm scope}
    (leftIH : RawStep.par leftRawTarget (RawTerm.cd leftRawSource))
    (rightIH : RawStep.par rightRawTarget (RawTerm.cd rightRawSource)) :
    RawStep.par (RawTerm.pathCompose leftRawTarget rightRawTarget)
      (RawTerm.cd (RawTerm.pathCompose leftRawSource
        rightRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.pathComposeCong leftIH rightIH

/-- `oeqTransCong` arm — D3.6-S5 pure cong on oeqTrans. -/
theorem RawStep.par.cd_lemma_oeqTransCong {scope : Nat}
    {firstRawSource firstRawTarget
     secondRawSource secondRawTarget : RawTerm scope}
    (firstIH : RawStep.par firstRawTarget (RawTerm.cd firstRawSource))
    (secondIH :
      RawStep.par secondRawTarget (RawTerm.cd secondRawSource)) :
    RawStep.par (RawTerm.oeqTrans firstRawTarget secondRawTarget)
      (RawTerm.cd (RawTerm.oeqTrans firstRawSource
        secondRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.oeqTransCong firstIH secondIH

/-- `equivComposeCong` arm — D3.6-S5 pure cong on equivCompose. -/
theorem RawStep.par.cd_lemma_equivComposeCong {scope : Nat}
    {firstRawSource firstRawTarget
     secondRawSource secondRawTarget : RawTerm scope}
    (firstIH : RawStep.par firstRawTarget (RawTerm.cd firstRawSource))
    (secondIH :
      RawStep.par secondRawTarget (RawTerm.cd secondRawSource)) :
    RawStep.par (RawTerm.equivCompose firstRawTarget secondRawTarget)
      (RawTerm.cd (RawTerm.equivCompose firstRawSource
        secondRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.equivComposeCong firstIH secondIH

/-- `uaToEquivCong` arm — pure cong. -/
theorem RawStep.par.cd_lemma_uaToEquivCong {scope : Nat}
    {innerRawSource innerRawTarget : RawTerm scope}
    (innerIH : RawStep.par innerRawTarget (RawTerm.cd innerRawSource)) :
    RawStep.par (RawTerm.uaToEquiv innerRawTarget)
      (RawTerm.cd (RawTerm.uaToEquiv innerRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.uaToEquivCong innerIH

/-- `idToEquivRefl` shallow refl-β — closed identity contractum. -/
theorem RawStep.par.cd_lemma_idToEquivRefl {scope : Nat}
    {witnessRawSource : RawTerm scope}
    (witnessTarget : RawTerm scope) :
    RawStep.par (RawTerm.idToEquiv (RawTerm.refl witnessTarget))
      (RawTerm.cd (RawTerm.idToEquiv (RawTerm.refl witnessRawSource))) := by
  simp only [RawTerm.cd, RawTerm.cdIdToEquivCase]
  exact RawStep.par.idToEquivRefl (RawStep.par.refl _)

/-- `idToEquivReflDeep` — proof develops to `refl`. -/
theorem RawStep.par.cd_lemma_idToEquivReflDeep {scope : Nat}
    {proofRawSource : RawTerm scope}
    {witnessTarget : RawTerm scope}
    (proofIH :
      RawStep.par (RawTerm.refl witnessTarget)
        (RawTerm.cd proofRawSource)) :
    RawStep.par (RawTerm.idToEquiv (RawTerm.refl witnessTarget))
      (RawTerm.cd (RawTerm.idToEquiv proofRawSource)) := by
  obtain ⟨witnessFinal, hCdEq, _witnessStep⟩ :=
    RawStep.par.refl_inv proofIH
  simp only [RawTerm.cd]
  rw [hCdEq]
  simp only [RawTerm.cdIdToEquivCase]
  exact RawStep.par.idToEquivRefl (RawStep.par.refl _)

end LeanFX2
