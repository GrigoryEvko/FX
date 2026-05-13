import LeanFX2.Reducibility.NeutralSNHott.HottJ

/-! # LeanFX2.Reducibility.NeutralSNHott.ElimVarShape

K12.20.AY var-shape eliminator SN preservation across the
eliminator surface: `modElim_var`, `glueElim_var`, `hcomp_var`,
`transp_var`, `refineElim_var`, `recordProj_var`,
`codataDest_var`, plus `natSucc`.

## Root status

Layer 3 metatheory leaf.  Second slice of NeutralSNHott. -/

namespace LeanFX2


/-- **K12.20.AY.1 neutral modElim SN preservation**.  Unary modal
destructor with variable inner term.  `modElim_inv` gives 2 arms:
cong (innerTerm → innerTarget) and βModElimIntro (innerTerm →
modIntro payloadTarget).  Variable inner: cong arm yields
`innerTarget = var position` via var_inv, then refl on the source
contradicts progressStep.2; β arm needs `var → modIntro _`,
defeated by var_inv + nomatch on `var = modIntro _`. -/
theorem RawTerm.modElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.modElim (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.modElim (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.modElim_inv progressStep.1 with
    ⟨innerTarget, targetEq, innerStep⟩
    | ⟨payloadTarget, _targetEq, innerStep⟩
  · have innerEq : innerTarget = RawTerm.var position :=
      (RawStep.par.var_inv innerStep)
    subst innerEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqModIntro :
          RawTerm.modIntro payloadTarget = RawTerm.var position :=
        (RawStep.par.var_inv innerStep)
      nomatch varEqModIntro)

/-- **K12.20.AY.2 neutral glueElim SN preservation**.  Unary cubical
destructor with variable glued value.  `glueElim_inv` gives 2 arms:
cong and βGlueElimIntro (gluedValue → glueIntro baseTarget
partialTarget).  Variable glued: cong arm contradicts
progressStep.2 via refl-on-source; β arm defeated by var_inv +
nomatch on `var = glueIntro _ _`. -/
theorem RawTerm.glueElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.glueElim (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.glueElim (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.glueElim_inv progressStep.1 with
    ⟨gluedTarget, targetEq, gluedStep⟩
    | ⟨baseTarget, partialTarget, _targetEq, gluedStep⟩
  · have gluedEq : gluedTarget = RawTerm.var position :=
      (RawStep.par.var_inv gluedStep)
    subst gluedEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqGlueIntro :
          RawTerm.glueIntro baseTarget partialTarget =
            RawTerm.var position :=
        (RawStep.par.var_inv gluedStep)
      nomatch varEqGlueIntro)

/-- **K12.20.AY.3 neutral hcomp SN preservation**.  Binary cubical
homogeneous-composition operator with variable in sides slot.
`hcomp_inv` is cong-only (no face-firing β at raw layer yet; full
Kan-op β reserved for cubical extension), so single-arm nested
induction on cap term's SN witness — directly analogous to
`equivApp_var`. -/
theorem RawTerm.hcomp_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {capTermRaw : RawTerm scope}
    (capIsSN : RawTerm.isStronglyNormalizing capTermRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.hcomp (RawTerm.var position) capTermRaw) := by
  induction capIsSN with
  | intro currentCap _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.hcomp (RawTerm.var position) currentCap) ?_
    intro target progressStep
    obtain ⟨sidesTarget, capTarget, targetEq, sidesStep, capStep⟩ :=
      RawStep.par.hcomp_inv progressStep.1
    have sidesEq : sidesTarget = RawTerm.var position :=
      (RawStep.par.var_inv sidesStep)
    subst sidesEq
    subst targetEq
    have capDistinct :
        currentCap ≠ capTarget := fun capEq =>
      progressStep.2 (congrArg (RawTerm.hcomp (RawTerm.var position)) capEq)
    exact inductiveHypothesis capTarget ⟨capStep, capDistinct⟩

/-- **K12.20.AY.4 neutral transp SN preservation**.  Binary cubical
transport with variable in path slot.  `transp_inv` is the heaviest
inversion in the kernel: 7 arms covering cong + 3 shape-equality β
rules (transpReflBeta on constant `pathLam _.weaken`, uaBeta on
`uaToEquiv _`, transpCompose on `pathCompose _ _`) + 3 deep β
counterparts where `pathTerm` par-steps to those ctors.  Variable
pathTerm: shape-equality arms defeated by direct nomatch on
`var = pathLam _ | uaToEquiv _ | pathCompose _ _`; deep arms
defeated by var_inv + nomatch on the resulting `ctor _ = var`. -/
theorem RawTerm.transp_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {sourceTermRaw : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing sourceTermRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.transp (RawTerm.var position) sourceTermRaw) := by
  induction sourceIsSN with
  | intro currentSource _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.transp (RawTerm.var position) currentSource) ?_
    intro target progressStep
    rcases RawStep.par.transp_inv progressStep.1 with
      ⟨pathTarget, sourceTarget, targetEq, pathStep, sourceStep⟩
      | ⟨_typeRawSource, _sourceTarget, pathEqRefl, _targetEq, _sourceStep⟩
      | ⟨_typeRawTarget, _sourceTarget, _targetEq, pathStepRefl, _sourceStep⟩
      | ⟨_proofRawSource, _proofRawTarget, _sourceTarget, pathEqUa,
          _targetEq, _proofStep, _sourceStep⟩
      | ⟨_proofRawTarget, _sourceTarget, _targetEq, pathStepUa,
          _sourceStep⟩
      | ⟨_leftRawSource, _leftRawTarget, _rightRawSource,
          _rightRawTarget, _sourceTarget, pathEqCompose, _targetEq,
          _leftStep, _rightStep, _sourceStep⟩
      | ⟨_leftRawTarget, _rightRawTarget, _sourceTarget, _targetEq,
          pathStepCompose, _sourceStep⟩
    · have pathEq : pathTarget = RawTerm.var position :=
        (RawStep.par.var_inv pathStep)
      subst pathEq
      subst targetEq
      have sourceDistinct :
          currentSource ≠ sourceTarget := fun sourceEq =>
        progressStep.2
          (congrArg (RawTerm.transp (RawTerm.var position)) sourceEq)
      exact inductiveHypothesis sourceTarget
        ⟨sourceStep, sourceDistinct⟩
    · exact (by nomatch pathEqRefl)
    · exact (by
        have varEqPathLam := (RawStep.par.var_inv pathStepRefl)
        nomatch varEqPathLam)
    · exact (by nomatch pathEqUa)
    · exact (by
        have varEqUaToEquiv := (RawStep.par.var_inv pathStepUa)
        nomatch varEqUaToEquiv)
    · exact (by nomatch pathEqCompose)
    · exact (by
        have varEqPathCompose := (RawStep.par.var_inv pathStepCompose)
        nomatch varEqPathCompose)

/-- **K12.20.BA.1 neutral refineElim SN preservation**.  Stage 1
completion (overlooked in K12.20.AY's "18/18" close-out — the
kernel has 20 unary/binary destructors with fireable β/ι rules at
the raw layer, including refineElim and recordProj which are
needed for K12.20.BC+ compound refine/record varShape work).
Unary refinement destructor with variable refined value;
refineElim_inv gives 2 arms: cong and βRefineElimIntro
(refinedValue → refineIntro valueTarget proofTarget).  Direct
`fst_var`-style template — cong arm contradicts progressStep.2
via refl-on-source; β arm defeated by `var_inv` + nomatch on
`var = refineIntro _ _`. -/
theorem RawTerm.refineElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.refineElim (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.refineElim (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.refineElim_inv progressStep.1 with
    ⟨refinedTarget, targetEq, refinedStep⟩
    | ⟨valueTarget, proofTarget, _targetEq, refinedStep⟩
  · have refinedEq : refinedTarget = RawTerm.var position :=
      (RawStep.par.var_inv refinedStep)
    subst refinedEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqRefineIntro :
          RawTerm.refineIntro valueTarget proofTarget =
            RawTerm.var position :=
        (RawStep.par.var_inv refinedStep)
      nomatch varEqRefineIntro)

/-- **K12.20.BA.2 neutral recordProj SN preservation**.  Sister to
`refineElim_var`; unary record-field projection with variable
record value.  `recordProj_inv` gives 2 arms: cong and
βRecordProjIntro (recordValue → recordIntro firstTarget).  Same
fst_var-style proof.  Closes Stage 1 honestly at 20/20 kernel
destructors. -/
theorem RawTerm.recordProj_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.recordProj (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.recordProj (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.recordProj_inv progressStep.1 with
    ⟨recordTarget, targetEq, recordStep⟩
    | ⟨firstTarget, _targetEq, recordStep⟩
  · have recordEq : recordTarget = RawTerm.var position :=
      (RawStep.par.var_inv recordStep)
    subst recordEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqRecordIntro :
          RawTerm.recordIntro firstTarget = RawTerm.var position :=
        (RawStep.par.var_inv recordStep)
      nomatch varEqRecordIntro)

/-- **K12.20.BA.3 neutral codataDest SN preservation**.  Unary
codata observation with variable codata value.  `codataDest_inv`
gives 2 arms: congruent observation and codata β after the codata
value develops to `codataUnfold`.  The congruent arm is reflexive
after `var_inv`; the β arm is impossible because a variable cannot
parallel-develop to `codataUnfold _ _`. -/
theorem RawTerm.codataDest_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.codataDest (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.codataDest (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.codataDest_inv progressStep.1 with
    ⟨codataTarget, targetEq, codataStep⟩
    | ⟨stateTarget, transitionTarget, _targetEq, codataStep⟩
  · have codataEq : codataTarget = RawTerm.var position :=
      (RawStep.par.var_inv codataStep)
    subst codataEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqCodataUnfold :
          RawTerm.codataUnfold stateTarget transitionTarget =
            RawTerm.var position :=
        (RawStep.par.var_inv codataStep)
      nomatch varEqCodataUnfold)

/-- `RawTerm.natSucc predecessor` is SN when predecessor is.  Same
proof pattern as `lam_isStronglyNormalizing`: structural induction
on predecessor's SN witness + step inversion via `natSucc_inv` +
ctor-injectivity for the disequality.  `natSucc` is also a unary
cong-only ctor at parallel reduction. -/
theorem RawTerm.natSucc_isStronglyNormalizing {scope : Nat}
    {predecessor : RawTerm scope}
    (predecessorIsSN : RawTerm.isStronglyNormalizing predecessor) :
    RawTerm.isStronglyNormalizing (RawTerm.natSucc predecessor) := by
  induction predecessorIsSN with
  | intro currentPredecessor _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.natSucc currentPredecessor) ?_
    intro target progressStep
    obtain ⟨predecessorTarget, targetEq, predecessorStep⟩ :=
      RawStep.par.natSucc_inv progressStep.1
    subst targetEq
    have predecessorDistinct :
        currentPredecessor ≠ predecessorTarget := fun predecessorEq =>
      progressStep.2 (congrArg RawTerm.natSucc predecessorEq)
    exact inductiveHypothesis predecessorTarget
      ⟨predecessorStep, predecessorDistinct⟩


end LeanFX2
