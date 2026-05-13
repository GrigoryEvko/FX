import LeanFX2.Reducibility.Neutral.NeutralCore

/-! # LeanFX2.Reducibility.Neutral.CubicalIdentityPreservation

Preservation of `RawTerm.IsNeutral` under one raw parallel step
for the cubical + identity family: `pathApp`, `glueElim`,
`hcomp`, `transp`, `idJ`, `oeqJ`, `idStrictRec`, `equivApp`,
`equivApply`.

## Root status

Layer 3 metatheory leaf.  Third slice of `Neutral`. -/

namespace LeanFX2


/-- Neutrality is preserved by one raw parallel step from `pathApp`
with a neutral path head. -/
theorem RawTerm.IsNeutral.pathApp_par_preserves {scope : Nat}
    {pathRaw intervalRaw targetRaw : RawTerm scope}
    (pathParPreserves :
      ∀ {pathTarget : RawTerm scope},
        RawStep.par pathRaw pathTarget →
        RawTerm.IsNeutral pathTarget)
    (parallelStep :
      RawStep.par (RawTerm.pathApp pathRaw intervalRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.pathApp_inv parallelStep with
    ⟨pathTarget, intervalTarget, targetEq,
      pathStep, _intervalStep⟩
    | ⟨bodyTarget, _intervalTarget, _targetEq,
        pathStep, _intervalStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.pathApp (pathParPreserves pathStep)
  · exact (RawTerm.IsNeutral.not_pathLam
      (pathParPreserves pathStep)
      (bodyRaw := bodyTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `glueElim`
with a neutral glued value. -/
theorem RawTerm.IsNeutral.glueElim_par_preserves {scope : Nat}
    {gluedRaw targetRaw : RawTerm scope}
    (gluedParPreserves :
      ∀ {gluedTarget : RawTerm scope},
        RawStep.par gluedRaw gluedTarget →
        RawTerm.IsNeutral gluedTarget)
    (parallelStep : RawStep.par (RawTerm.glueElim gluedRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.glueElim_inv parallelStep with
    ⟨gluedTarget, targetEq, gluedStep⟩
    | ⟨baseTarget, partialTarget, _targetEq, gluedStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.glueElim (gluedParPreserves gluedStep)
  · exact (RawTerm.IsNeutral.not_glueIntro
      (gluedParPreserves gluedStep)
      (baseRaw := baseTarget) (partialRaw := partialTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `hcomp`
with neutral sides. -/
theorem RawTerm.IsNeutral.hcomp_par_preserves {scope : Nat}
    {sidesRaw capRaw targetRaw : RawTerm scope}
    (sidesParPreserves :
      ∀ {sidesTarget : RawTerm scope},
        RawStep.par sidesRaw sidesTarget →
        RawTerm.IsNeutral sidesTarget)
    (parallelStep : RawStep.par (RawTerm.hcomp sidesRaw capRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨sidesTarget, capTarget, targetEq,
      sidesStep, _capStep⟩ :=
    RawStep.par.hcomp_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.hcomp (sidesParPreserves sidesStep)

/-- Neutrality is preserved by one raw parallel step from `transp`
with a neutral path line.  The non-congruent D3.6 arms are impossible
because the path source or path target would have to be canonical. -/
theorem RawTerm.IsNeutral.transp_par_preserves {scope : Nat}
    {pathRaw sourceRaw targetRaw : RawTerm scope}
    (pathIsNeutral : RawTerm.IsNeutral pathRaw)
    (pathParPreserves :
      ∀ {pathTarget : RawTerm scope},
        RawStep.par pathRaw pathTarget →
        RawTerm.IsNeutral pathTarget)
    (parallelStep : RawStep.par (RawTerm.transp pathRaw sourceRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.transp_inv parallelStep with
    ⟨pathTarget, sourceTarget, targetEq,
      pathStep, _sourceStep⟩
    | ⟨typeRawSource, _sourceTarget, pathEq,
        _targetEq, _sourceStep⟩
    | ⟨typeRawTarget, _sourceTarget, _targetEq,
        pathStep, _sourceStep⟩
    | ⟨proofRawSource, _proofRawTarget, _sourceTarget,
        pathEq, _targetEq, _proofStep, _sourceStep⟩
    | ⟨proofRawTarget, _sourceTarget, _targetEq,
        pathStep, _sourceStep⟩
    | ⟨leftRawSource, _leftRawTarget, rightRawSource,
        _rightRawTarget, _sourceTarget, pathEq,
        _targetEq, _leftStep, _rightStep, _sourceStep⟩
    | ⟨leftRawTarget, rightRawTarget, _sourceTarget, _targetEq,
        pathStep, _sourceStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.transp (pathParPreserves pathStep)
  · exact (RawTerm.IsNeutral.not_pathLam pathIsNeutral
      (bodyRaw := typeRawSource.weaken) pathEq).elim
  · exact (RawTerm.IsNeutral.not_pathLam
      (pathParPreserves pathStep)
      (bodyRaw := typeRawTarget.weaken) rfl).elim
  · exact (RawTerm.IsNeutral.not_uaToEquiv pathIsNeutral
      (proofRaw := proofRawSource) pathEq).elim
  · exact (RawTerm.IsNeutral.not_uaToEquiv
      (pathParPreserves pathStep)
      (proofRaw := proofRawTarget) rfl).elim
  · exact (RawTerm.IsNeutral.not_pathCompose pathIsNeutral
      (leftRaw := leftRawSource) (rightRaw := rightRawSource)
      pathEq).elim
  · exact (RawTerm.IsNeutral.not_pathCompose
      (pathParPreserves pathStep)
      (leftRaw := leftRawTarget) (rightRaw := rightRawTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `idJ`
with a neutral equality witness. -/
theorem RawTerm.IsNeutral.idJ_par_preserves {scope : Nat}
    {baseRaw witnessRaw targetRaw : RawTerm scope}
    (witnessParPreserves :
      ∀ {witnessTarget : RawTerm scope},
        RawStep.par witnessRaw witnessTarget →
        RawTerm.IsNeutral witnessTarget)
    (parallelStep : RawStep.par (RawTerm.idJ baseRaw witnessRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.idJ_inv parallelStep with
    ⟨baseTarget, witnessTarget, targetEq,
      _baseStep, witnessStep⟩
    | ⟨witnessTarget, _baseTarget, _targetEq,
        witnessStep, _baseStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.idJ (witnessParPreserves witnessStep)
  · exact (RawTerm.IsNeutral.not_refl
      (witnessParPreserves witnessStep)
      (witnessRaw := witnessTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `oeqJ`
with a neutral observational-equality witness. -/
theorem RawTerm.IsNeutral.oeqJ_par_preserves {scope : Nat}
    {baseRaw witnessRaw targetRaw : RawTerm scope}
    (witnessParPreserves :
      ∀ {witnessTarget : RawTerm scope},
        RawStep.par witnessRaw witnessTarget →
        RawTerm.IsNeutral witnessTarget)
    (parallelStep : RawStep.par (RawTerm.oeqJ baseRaw witnessRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨baseTarget, witnessTarget, targetEq,
      _baseStep, witnessStep⟩ :=
    RawStep.par.oeqJ_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.oeqJ (witnessParPreserves witnessStep)

/-- Neutrality is preserved by one raw parallel step from `idStrictRec`
with a neutral strict-identity witness. -/
theorem RawTerm.IsNeutral.idStrictRec_par_preserves {scope : Nat}
    {baseRaw witnessRaw targetRaw : RawTerm scope}
    (witnessParPreserves :
      ∀ {witnessTarget : RawTerm scope},
        RawStep.par witnessRaw witnessTarget →
        RawTerm.IsNeutral witnessTarget)
    (parallelStep :
      RawStep.par (RawTerm.idStrictRec baseRaw witnessRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.idStrictRec_inv parallelStep with
    ⟨baseTarget, witnessTarget, targetEq,
      _baseStep, witnessStep⟩
    | ⟨witnessTarget, _baseTarget, _targetEq,
        witnessStep, _baseStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.idStrictRec
      (witnessParPreserves witnessStep)
  · exact (RawTerm.IsNeutral.not_idStrictRefl
      (witnessParPreserves witnessStep)
      (witnessRaw := witnessTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `equivApp`
with a neutral equivalence head. -/
theorem RawTerm.IsNeutral.equivApp_par_preserves {scope : Nat}
    {equivRaw argumentRaw targetRaw : RawTerm scope}
    (equivParPreserves :
      ∀ {equivTarget : RawTerm scope},
        RawStep.par equivRaw equivTarget →
        RawTerm.IsNeutral equivTarget)
    (parallelStep :
      RawStep.par (RawTerm.equivApp equivRaw argumentRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨equivTarget, argumentTarget, targetEq,
      equivStep, _argumentStep⟩ :=
    RawStep.par.equivApp_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.equivApp (equivParPreserves equivStep)

/-- Neutrality is preserved by one raw parallel step from `equivApply`
with a neutral equivalence head.  The univalence-reflexivity β arms are
impossible because the equivalence source or target would have to be
`uaToEquiv _`. -/
theorem RawTerm.IsNeutral.equivApply_par_preserves {scope : Nat}
    {equivRaw argumentRaw targetRaw : RawTerm scope}
    (equivIsNeutral : RawTerm.IsNeutral equivRaw)
    (equivParPreserves :
      ∀ {equivTarget : RawTerm scope},
        RawStep.par equivRaw equivTarget →
        RawTerm.IsNeutral equivTarget)
    (parallelStep :
      RawStep.par (RawTerm.equivApply equivRaw argumentRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.equivApply_inv parallelStep with
    ⟨equivTarget, argumentTarget, targetEq,
      equivStep, _argumentStep⟩
    | ⟨witnessSource, _witnessTarget, _sourceTarget,
        equivEq, _targetEq, _witnessStep, _argumentStep⟩
    | ⟨witnessTarget, _sourceTarget, _targetEq,
        equivStep, _argumentStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.equivApply
      (equivParPreserves equivStep)
  · exact (RawTerm.IsNeutral.not_uaToEquiv equivIsNeutral
      (proofRaw := RawTerm.oeqRefl witnessSource) equivEq).elim
  · exact (RawTerm.IsNeutral.not_uaToEquiv
      (equivParPreserves equivStep)
      (proofRaw := RawTerm.oeqRefl witnessTarget) rfl).elim

end LeanFX2
