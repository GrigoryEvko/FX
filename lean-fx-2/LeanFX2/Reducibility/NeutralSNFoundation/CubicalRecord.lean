import LeanFX2.Reducibility.SNHelpers
import LeanFX2.Reducibility.Neutral

/-! # LeanFX2.Reducibility.NeutralSNFoundation.CubicalRecord

Cubical + record / refine / codata SN preservation.  Covers
`pathApp_var` / `pathApp_neutral`, `glueElim_neutral`,
`refineElim_neutral`, `recordProj_neutral`, and
`codataDest_neutral`.

## Root status

Layer 3 metatheory leaf.  Fourth slice of NeutralSNFoundation. -/

namespace LeanFX2

/-- **K12.20.AX.1 neutral pathApp SN preservation**.  Direct analogue
of `app_var`: var sits in the path-term slot, interval argument is
SN witness.  `pathApp_inv` gives 2 arms (cong + β); β arm requires
`pathTerm → pathLam _`, defeated by `var_inv` + nomatch on the
resulting `var = pathLam _` equation. -/
theorem RawTerm.pathApp_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {intervalArgRaw : RawTerm scope}
    (intervalIsSN : RawTerm.isStronglyNormalizing intervalArgRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.pathApp (RawTerm.var position) intervalArgRaw) := by
  induction intervalIsSN with
  | intro currentInterval _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.pathApp (RawTerm.var position) currentInterval) ?_
    intro target progressStep
    rcases RawStep.par.pathApp_inv progressStep.1 with
      ⟨pathTarget, intervalTarget, targetEq, pathStep, intervalStep⟩
      | ⟨bodyTarget, _intervalTarget, _targetEq, pathStep, _intervalStep⟩
    · have pathEq : pathTarget = RawTerm.var position :=
        (RawStep.par.var_inv pathStep)
      subst pathEq
      subst targetEq
      have intervalDistinct :
          currentInterval ≠ intervalTarget := fun intervalEq =>
        progressStep.2
          (congrArg (RawTerm.pathApp (RawTerm.var position)) intervalEq)
      exact inductiveHypothesis intervalTarget
        ⟨intervalStep, intervalDistinct⟩
    · exact (by
        have varEqPathLam :
            RawTerm.pathLam bodyTarget = RawTerm.var position :=
          (RawStep.par.var_inv pathStep)
        nomatch varEqPathLam)

/-- Path application with a neutral path head is strongly normalizing
when both the path head and interval argument are strongly normalizing.

The path beta arms are impossible because every parallel reduct of the
neutral head stays neutral, and neutral terms are never `pathLam`-
shaped.  The congruence arm recurses on head progress or interval
progress. -/
theorem RawTerm.pathApp_neutral_isStronglyNormalizing {scope : Nat}
    {pathRaw intervalArgRaw : RawTerm scope}
    (pathIsNeutral : RawTerm.IsNeutral pathRaw)
    (pathIsSN : RawTerm.isStronglyNormalizing pathRaw)
    (intervalIsSN : RawTerm.isStronglyNormalizing intervalArgRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.pathApp pathRaw intervalArgRaw) := by
  induction pathIsSN generalizing intervalArgRaw with
  | intro currentPath _ pathInduction =>
    induction intervalIsSN with
    | intro currentInterval intervalClosure intervalInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pathApp currentPath currentInterval) ?_
      intro target progressStep
      rcases RawStep.par.pathApp_inv progressStep.1 with
        ⟨pathTarget, intervalTarget, targetEq, pathStep, intervalStep⟩
        | ⟨bodyTarget, _intervalTarget, _targetEq,
            pathStep, _intervalStep⟩
      · subst targetEq
        have pathTargetIsNeutral : RawTerm.IsNeutral pathTarget :=
          RawTerm.IsNeutral.par_preserves pathIsNeutral pathStep
        have intervalTargetIsSN :
            RawTerm.isStronglyNormalizing intervalTarget := by
          by_cases intervalEq : currentInterval = intervalTarget
          · subst intervalEq
            exact RawTerm.isStronglyNormalizing.intro
              currentInterval intervalClosure
          · exact intervalClosure intervalTarget
              ⟨intervalStep, intervalEq⟩
        by_cases pathEq : currentPath = pathTarget
        · subst pathEq
          by_cases intervalEq : currentInterval = intervalTarget
          · subst intervalEq
            exact (progressStep.2 rfl).elim
          · exact intervalInduction intervalTarget
              ⟨intervalStep, intervalEq⟩
        · exact pathInduction pathTarget
            ⟨pathStep, pathEq⟩
            pathTargetIsNeutral
            intervalTargetIsSN
      · exact (RawTerm.IsNeutral.not_pathLam
          (RawTerm.IsNeutral.par_preserves pathIsNeutral pathStep)
          (bodyRaw := bodyTarget) rfl).elim

/-- Glue elimination with a neutral glued value is strongly normalizing
when the glued value is strongly normalizing.

The Glue beta arms are impossible because every parallel reduct of the
neutral glued value stays neutral, and neutral terms are never
`glueIntro`-shaped.  The congruence arm recurses on glued-value
progress. -/
theorem RawTerm.glueElim_neutral_isStronglyNormalizing {scope : Nat}
    {gluedRaw : RawTerm scope}
    (gluedIsNeutral : RawTerm.IsNeutral gluedRaw)
    (gluedIsSN : RawTerm.isStronglyNormalizing gluedRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.glueElim gluedRaw) := by
  induction gluedIsSN with
  | intro currentGlued _ gluedInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.glueElim currentGlued) ?_
    intro target progressStep
    rcases RawStep.par.glueElim_inv progressStep.1 with
      ⟨gluedTarget, targetEq, gluedStep⟩
      | ⟨baseTarget, partialTarget, _targetEq, gluedStep⟩
    · have gluedTargetIsNeutral : RawTerm.IsNeutral gluedTarget :=
        RawTerm.IsNeutral.par_preserves gluedIsNeutral gluedStep
      by_cases gluedEq : currentGlued = gluedTarget
      · subst gluedEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact gluedInduction gluedTarget
          ⟨gluedStep, gluedEq⟩ gluedTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_glueIntro
        (RawTerm.IsNeutral.par_preserves gluedIsNeutral gluedStep)
        (baseRaw := baseTarget) (partialRaw := partialTarget) rfl).elim

/-- Refinement elimination with a neutral refined value is strongly
normalizing when the refined value is strongly normalizing.

The refinement beta arms are impossible because every parallel reduct
of the neutral refined value stays neutral, and neutral terms are never
`refineIntro`-shaped.  The congruence arm recurses on refined-value
progress. -/
theorem RawTerm.refineElim_neutral_isStronglyNormalizing {scope : Nat}
    {refinedRaw : RawTerm scope}
    (refinedIsNeutral : RawTerm.IsNeutral refinedRaw)
    (refinedIsSN : RawTerm.isStronglyNormalizing refinedRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.refineElim refinedRaw) := by
  induction refinedIsSN with
  | intro currentRefined _ refinedInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.refineElim currentRefined) ?_
    intro target progressStep
    rcases RawStep.par.refineElim_inv progressStep.1 with
      ⟨refinedTarget, targetEq, refinedStep⟩
      | ⟨valueTarget, proofTarget, _targetEq, refinedStep⟩
    · have refinedTargetIsNeutral :
          RawTerm.IsNeutral refinedTarget :=
        RawTerm.IsNeutral.par_preserves refinedIsNeutral refinedStep
      by_cases refinedEq : currentRefined = refinedTarget
      · subst refinedEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact refinedInduction refinedTarget
          ⟨refinedStep, refinedEq⟩ refinedTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_refineIntro
        (RawTerm.IsNeutral.par_preserves refinedIsNeutral refinedStep)
        (valueRaw := valueTarget) (proofRaw := proofTarget) rfl).elim

/-- Record projection with a neutral record value is strongly
normalizing when the record value is strongly normalizing.

The record beta arms are impossible because every parallel reduct of
the neutral record value stays neutral, and neutral terms are never
`recordIntro`-shaped.  The congruence arm recurses on record-value
progress. -/
theorem RawTerm.recordProj_neutral_isStronglyNormalizing {scope : Nat}
    {recordRaw : RawTerm scope}
    (recordIsNeutral : RawTerm.IsNeutral recordRaw)
    (recordIsSN : RawTerm.isStronglyNormalizing recordRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.recordProj recordRaw) := by
  induction recordIsSN with
  | intro currentRecord _ recordInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.recordProj currentRecord) ?_
    intro target progressStep
    rcases RawStep.par.recordProj_inv progressStep.1 with
      ⟨recordTarget, targetEq, recordStep⟩
      | ⟨fieldTarget, _targetEq, recordStep⟩
    · have recordTargetIsNeutral :
          RawTerm.IsNeutral recordTarget :=
        RawTerm.IsNeutral.par_preserves recordIsNeutral recordStep
      by_cases recordEq : currentRecord = recordTarget
      · subst recordEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact recordInduction recordTarget
          ⟨recordStep, recordEq⟩ recordTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_recordIntro
        (RawTerm.IsNeutral.par_preserves recordIsNeutral recordStep)
        (fieldRaw := fieldTarget) rfl).elim

/-- Codata observation with a neutral codata value is strongly
normalizing when the codata value is strongly normalizing.

The codata beta arms are impossible because every parallel reduct of
the neutral codata value stays neutral, and neutral terms are never
`codataUnfold`-shaped.  The congruence arm recurses on codata-value
progress. -/
theorem RawTerm.codataDest_neutral_isStronglyNormalizing {scope : Nat}
    {codataRaw : RawTerm scope}
    (codataIsNeutral : RawTerm.IsNeutral codataRaw)
    (codataIsSN : RawTerm.isStronglyNormalizing codataRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.codataDest codataRaw) := by
  induction codataIsSN with
  | intro currentCodata _ codataInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.codataDest currentCodata) ?_
    intro target progressStep
    rcases RawStep.par.codataDest_inv progressStep.1 with
      ⟨codataTarget, targetEq, codataStep⟩
      | ⟨stateTarget, transitionTarget, _targetEq, codataStep⟩
    · have codataTargetIsNeutral :
          RawTerm.IsNeutral codataTarget :=
        RawTerm.IsNeutral.par_preserves codataIsNeutral codataStep
      by_cases codataEq : currentCodata = codataTarget
      · subst codataEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact codataInduction codataTarget
          ⟨codataStep, codataEq⟩ codataTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_codataUnfold
        (RawTerm.IsNeutral.par_preserves codataIsNeutral codataStep)
        (initialRaw := stateTarget) (transitionRaw := transitionTarget)
        rfl).elim


end LeanFX2
