import LeanFX2.Reducibility.NeutralSNFoundation

/-! # LeanFX2.Reducibility.NeutralSNHott — K12.20.C HOTT-J recursors

Part 2 of K12.20.C.  Covers the HOTT identity-type J recursors
(`idJ`, `oeqJ`, `idStrictRec`) plus advanced destructor SN
preservation and the parametric inductive ctors (`listType` /
`optionType` / `eitherType`).

## What ships

* `RawTerm.idJ_isStronglyNormalizing` + neutral / var variants —
  HoTT identity J recursor SN preservation.
* `RawTerm.oeqJ_isStronglyNormalizing` + neutral / var variants —
  observational equality J SN preservation.
* `RawTerm.idStrictRec_isStronglyNormalizing` + neutral / var
  variants — strict identity recursor SN preservation.
* Container destructor SN (listElim_listNil, optionMatch_optionSome,
  eitherMatch_eitherInl/Inr SN preservation when applied to the
  canonical introducer).
* Typed mirrors via `Term.X_isStronglyNormalizing` wrappers.

## Root status

Layer 3 metatheory leaf.  Continues the K12.20.C cascade.
Consumed by `NeutralSNIntro` and downstream typed-CR2 modules. -/

namespace LeanFX2


/-- **K12.20.AX.4 neutral oeqJ SN preservation**.  Observational
equality J eliminator with variable witness.  `oeqJ_inv` is
cong-only (no ι rule at raw layer yet; oeq-style witness elimination
deferred), so no nomatch defense needed.  Same proof pattern as
`equivApp_var` but with var in the SECOND slot. -/
theorem RawTerm.oeqJ_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.oeqJ baseCaseRaw (RawTerm.var position)) := by
  induction baseCaseIsSN with
  | intro currentBase _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.oeqJ currentBase (RawTerm.var position)) ?_
    intro target progressStep
    obtain ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩ :=
      RawStep.par.oeqJ_inv progressStep.1
    have witnessEq : witnessTarget = RawTerm.var position :=
      (RawStep.par.var_inv witnessStep)
    subst witnessEq
    subst targetEq
    have baseDistinct :
        currentBase ≠ baseTarget := fun baseEq =>
      progressStep.2
        (congrArg (fun base => RawTerm.oeqJ base (RawTerm.var position))
          baseEq)
    exact inductiveHypothesis baseTarget
      ⟨baseStep, baseDistinct⟩

/-- Observational-equality eliminator SN preservation.  Unlike
`idJ` and `idStrictRec`, the current raw `oeqJ` fragment has no
refl-ι firing rule; `RawStep.par.oeqJ_inv` is pure congruence over
the base case and witness. -/
theorem RawTerm.oeqJ_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    ∀ {witnessRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing witnessRaw →
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqJ baseCaseRaw witnessRaw) := by
  induction baseCaseIsSN with
  | intro currentBase _ baseIH =>
    intro witnessRaw witnessIsSN
    induction witnessIsSN with
    | intro currentWitness witnessClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.oeqJ currentBase currentWitness) ?_
      intro target progressStep
      obtain ⟨baseTarget, witnessTarget, targetEq,
              baseStep, witnessStep⟩ :=
        RawStep.par.oeqJ_inv progressStep.1
      subst targetEq
      by_cases baseEq : currentBase = baseTarget
      · subst baseEq
        have witnessDistinct :
            currentWitness ≠ witnessTarget := fun witnessEq =>
          progressStep.2
            (congrArg (RawTerm.oeqJ currentBase) witnessEq)
        exact innerIH witnessTarget ⟨witnessStep, witnessDistinct⟩
      · have baseProgress :
            RawStep.parProgress currentBase baseTarget :=
          ⟨baseStep, baseEq⟩
        by_cases witnessEq : currentWitness = witnessTarget
        · subst witnessEq
          exact baseIH baseTarget baseProgress
            (RawTerm.isStronglyNormalizing.intro currentWitness
              witnessClosure)
        · exact baseIH baseTarget baseProgress
            (witnessClosure witnessTarget ⟨witnessStep, witnessEq⟩)

/-- Observational-equality eliminator with a neutral witness is
strongly normalizing when the witness and base case are strongly
normalizing.

The current raw `oeqJ` fragment is congruence-only, so this helper
records the neutral CR3 shape without a canonical-exclusion branch. -/
theorem RawTerm.oeqJ_neutral_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw witnessRaw : RawTerm scope}
    (witnessIsNeutral : RawTerm.IsNeutral witnessRaw)
    (witnessIsSN : RawTerm.isStronglyNormalizing witnessRaw)
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.oeqJ baseCaseRaw witnessRaw) := by
  induction witnessIsSN generalizing baseCaseRaw with
  | intro currentWitness _ witnessInduction =>
    induction baseCaseIsSN with
    | intro currentBase baseClosure baseInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.oeqJ currentBase currentWitness) ?_
      intro target progressStep
      obtain ⟨baseTarget, witnessTarget, targetEq,
              baseStep, witnessStep⟩ :=
        RawStep.par.oeqJ_inv progressStep.1
      subst targetEq
      have witnessTargetIsNeutral :
          RawTerm.IsNeutral witnessTarget :=
        RawTerm.IsNeutral.par_preserves witnessIsNeutral witnessStep
      have baseTargetIsSN :
          RawTerm.isStronglyNormalizing baseTarget := by
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          exact RawTerm.isStronglyNormalizing.intro
            currentBase baseClosure
        · exact baseClosure baseTarget ⟨baseStep, baseEq⟩
      by_cases witnessEq : currentWitness = witnessTarget
      · subst witnessEq
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          exact (progressStep.2 rfl).elim
        · exact baseInduction baseTarget ⟨baseStep, baseEq⟩
      · exact witnessInduction witnessTarget
          ⟨witnessStep, witnessEq⟩
          witnessTargetIsNeutral baseTargetIsSN

/-- Identity eliminator SN preservation.  Unlike `oeqJ`, `idJ` has
refl-ι rules, so the iota arm returns the reduced base case directly.
The congruence arm follows the same nested-SN induction pattern as
`RawTerm.oeqJ_isStronglyNormalizing`. -/
theorem RawTerm.idJ_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    ∀ {witnessRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing witnessRaw →
      RawTerm.isStronglyNormalizing
        (RawTerm.idJ baseCaseRaw witnessRaw) := by
  induction baseCaseIsSN with
  | intro currentBase baseClosure baseIH =>
    intro witnessRaw witnessIsSN
    induction witnessIsSN with
    | intro currentWitness witnessClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.idJ currentBase currentWitness) ?_
      intro target progressStep
      cases RawStep.par.idJ_inv progressStep.1 with
      | inl congruentStep =>
        rcases congruentStep with
          ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
        subst targetEq
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          have witnessDistinct :
              currentWitness ≠ witnessTarget := fun witnessEq =>
            progressStep.2
              (congrArg (RawTerm.idJ currentBase) witnessEq)
          exact innerIH witnessTarget ⟨witnessStep, witnessDistinct⟩
        · have baseProgress :
              RawStep.parProgress currentBase baseTarget :=
            ⟨baseStep, baseEq⟩
          by_cases witnessEq : currentWitness = witnessTarget
          · subst witnessEq
            exact baseIH baseTarget baseProgress
              (RawTerm.isStronglyNormalizing.intro currentWitness
                witnessClosure)
          · exact baseIH baseTarget baseProgress
              (witnessClosure witnessTarget ⟨witnessStep, witnessEq⟩)
      | inr iotaStep =>
        rcases iotaStep with
          ⟨_witnessRaw, baseTarget, targetEq, _witnessStep, baseStep⟩
        rw [targetEq]
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          exact RawTerm.isStronglyNormalizing.intro currentBase baseClosure
        · exact baseClosure baseTarget ⟨baseStep, baseEq⟩

/-- **K12.20.AX.5 neutral idStrictRec SN preservation**.  Strict-id
recursor with variable witness.  `idStrictRec_inv` gives 2 arms
(cong + iotaIdStrictRecRefl); ι arm requires
`witness → idStrictRefl _`, defeated by `var_inv` + nomatch on
`var = idStrictRefl _`. -/
theorem RawTerm.idStrictRec_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.idStrictRec baseCaseRaw (RawTerm.var position)) := by
  induction baseCaseIsSN with
  | intro currentBase _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.idStrictRec currentBase (RawTerm.var position)) ?_
    intro target progressStep
    rcases RawStep.par.idStrictRec_inv progressStep.1 with
      ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
      | ⟨reflRawArgument, _baseTarget, _targetEq, witnessStep, _baseStep⟩
    · have witnessEq : witnessTarget = RawTerm.var position :=
        (RawStep.par.var_inv witnessStep)
      subst witnessEq
      subst targetEq
      have baseDistinct :
          currentBase ≠ baseTarget := fun baseEq =>
        progressStep.2
          (congrArg
            (fun base => RawTerm.idStrictRec base (RawTerm.var position))
            baseEq)
      exact inductiveHypothesis baseTarget
        ⟨baseStep, baseDistinct⟩
    · exact (by
        have varEqIdStrictRefl :
            RawTerm.var position = RawTerm.idStrictRefl reflRawArgument :=
          (RawStep.par.var_inv witnessStep).symm
        nomatch varEqIdStrictRefl)

/-- Strict identity recursor SN preservation.  This mirrors
`RawTerm.idJ_isStronglyNormalizing`, with the strict reflexivity
constructor in the iota arm. -/
theorem RawTerm.idStrictRec_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    ∀ {witnessRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing witnessRaw →
      RawTerm.isStronglyNormalizing
        (RawTerm.idStrictRec baseCaseRaw witnessRaw) := by
  induction baseCaseIsSN with
  | intro currentBase baseClosure baseIH =>
    intro witnessRaw witnessIsSN
    induction witnessIsSN with
    | intro currentWitness witnessClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.idStrictRec currentBase currentWitness) ?_
      intro target progressStep
      cases RawStep.par.idStrictRec_inv progressStep.1 with
      | inl congruentStep =>
        rcases congruentStep with
          ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
        subst targetEq
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          have witnessDistinct :
              currentWitness ≠ witnessTarget := fun witnessEq =>
            progressStep.2
              (congrArg (RawTerm.idStrictRec currentBase) witnessEq)
          exact innerIH witnessTarget ⟨witnessStep, witnessDistinct⟩
        · have baseProgress :
              RawStep.parProgress currentBase baseTarget :=
            ⟨baseStep, baseEq⟩
          by_cases witnessEq : currentWitness = witnessTarget
          · subst witnessEq
            exact baseIH baseTarget baseProgress
              (RawTerm.isStronglyNormalizing.intro currentWitness
                witnessClosure)
          · exact baseIH baseTarget baseProgress
              (witnessClosure witnessTarget ⟨witnessStep, witnessEq⟩)
      | inr iotaStep =>
        rcases iotaStep with
          ⟨_reflRawArgument, baseTarget, targetEq, _witnessStep, baseStep⟩
        rw [targetEq]
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          exact RawTerm.isStronglyNormalizing.intro currentBase baseClosure
        · exact baseClosure baseTarget ⟨baseStep, baseEq⟩

/-- Strict identity recursor with a neutral witness is strongly
normalizing when the witness and base case are strongly normalizing.

The strict-refl ι arm is impossible because every parallel reduct of
the neutral witness stays neutral, and neutral terms are never
`idStrictRefl` shaped.  The typed mode witness for `Term.idStrictRec`
is absent at the raw layer; this helper tracks only the computational
base case and identity witness. -/
theorem RawTerm.idStrictRec_neutral_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw witnessRaw : RawTerm scope}
    (witnessIsNeutral : RawTerm.IsNeutral witnessRaw)
    (witnessIsSN : RawTerm.isStronglyNormalizing witnessRaw)
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.idStrictRec baseCaseRaw witnessRaw) := by
  induction witnessIsSN generalizing baseCaseRaw with
  | intro currentWitness _ witnessInduction =>
    induction baseCaseIsSN with
    | intro currentBase baseClosure baseInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.idStrictRec currentBase currentWitness) ?_
      intro target progressStep
      rcases RawStep.par.idStrictRec_inv progressStep.1 with
        ⟨baseTarget, witnessTarget, targetEq,
          baseStep, witnessStep⟩
        | ⟨reflRawArgument, _baseTarget, _targetEq,
            witnessStep, _baseStep⟩
      · subst targetEq
        have witnessTargetIsNeutral :
            RawTerm.IsNeutral witnessTarget :=
          RawTerm.IsNeutral.par_preserves witnessIsNeutral witnessStep
        have baseTargetIsSN :
            RawTerm.isStronglyNormalizing baseTarget := by
          by_cases baseEq : currentBase = baseTarget
          · subst baseEq
            exact RawTerm.isStronglyNormalizing.intro
              currentBase baseClosure
          · exact baseClosure baseTarget ⟨baseStep, baseEq⟩
        by_cases witnessEq : currentWitness = witnessTarget
        · subst witnessEq
          by_cases baseEq : currentBase = baseTarget
          · subst baseEq
            exact (progressStep.2 rfl).elim
          · exact baseInduction baseTarget ⟨baseStep, baseEq⟩
        · exact witnessInduction witnessTarget
            ⟨witnessStep, witnessEq⟩
            witnessTargetIsNeutral baseTargetIsSN
      · exact (RawTerm.IsNeutral.not_idStrictRefl
          (RawTerm.IsNeutral.par_preserves witnessIsNeutral witnessStep)
          (witnessRaw := reflRawArgument) rfl).elim

/-- **K12.20.U3.monotone weak-J arm**: HoTT identity
reducibility weakens without a full world-monotone recursive
candidate.  The closure output is SN, so the extended-context J
case is rebuilt from raw `idJ` SN preservation. -/
theorem Reducible.weaken_id
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    {sourceTerm :
      Term context (Ty.id carrierType leftEndpoint rightEndpoint) sourceRaw}
    (sourceReducible :
      Reducible (Ty.id carrierType leftEndpoint rightEndpoint) sourceTerm) :
    Reducible ((Ty.id carrierType leftEndpoint rightEndpoint).weaken)
      (Term.weaken newType sourceTerm) := by
  refine
    ⟨Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1, ?_⟩
  intro _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.idJ_isStronglyNormalizing baseIsSN
    (Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1)

/-- **K12.20.U3.monotone weak-J arm**: observational equality
reducibility weakens by rebuilding the SN-output eliminator closure
from raw `oeqJ` SN preservation. -/
theorem Reducible.weaken_oeq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    {sourceTerm :
      Term context (Ty.oeq carrierType leftEndpoint rightEndpoint) sourceRaw}
    (sourceReducible :
      Reducible (Ty.oeq carrierType leftEndpoint rightEndpoint) sourceTerm) :
    Reducible ((Ty.oeq carrierType leftEndpoint rightEndpoint).weaken)
      (Term.weaken newType sourceTerm) := by
  refine
    ⟨Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1, ?_⟩
  intro _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.oeqJ_isStronglyNormalizing baseIsSN
    (Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1)

/-- **K12.20.U3.monotone weak-J arm**: strict identity
reducibility weakens by rebuilding the strict recursor's SN-output
closure from raw `idStrictRec` SN preservation. -/
theorem Reducible.weaken_idStrict
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    {sourceTerm :
      Term context (Ty.idStrict carrierType leftEndpoint rightEndpoint) sourceRaw}
    (sourceReducible :
      Reducible (Ty.idStrict carrierType leftEndpoint rightEndpoint) sourceTerm) :
    Reducible ((Ty.idStrict carrierType leftEndpoint rightEndpoint).weaken)
      (Term.weaken newType sourceTerm) := by
  refine
    ⟨Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1, ?_⟩
  intro _modeIsStrict _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.idStrictRec_isStronglyNormalizing baseIsSN
    (Term.isStronglyNormalizing_weaken (newType := newType)
      sourceReducible.1)

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

/-- Nat-zero ι SN expansion for `natElim`.

For a canonical zero scrutinee, `natElim` reduces to the zero branch.
The successor branch remains in the statement because congruent
reductions may step under it before the ι rule fires. -/
theorem RawTerm.natElim_natZero_isStronglyNormalizing
    {scope : Nat}
    {zeroBranch : RawTerm scope}
    (zeroIsSN : RawTerm.isStronglyNormalizing zeroBranch) :
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natElim RawTerm.natZero zeroBranch succBranch) := by
  induction zeroIsSN with
  | intro currentZero zeroClosure zeroIH =>
    intro succBranch succIsSN
    induction succIsSN with
    | intro currentSucc succClosure succIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.natElim RawTerm.natZero currentZero currentSucc) ?_
      intro target progressStep
      rcases RawStep.par.natElim_inv progressStep.1 with
        ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
          scrutineeStep, zeroStep, succStep⟩
        | ⟨zeroTarget, targetEq, _scrutineeStep, zeroStep⟩
        | ⟨predecessorTarget, _succTarget, _targetEq,
            scrutineeStep, _succStep⟩
      · have scrutineeTargetEq :
            scrutineeTarget = (RawTerm.natZero : RawTerm scope) :=
          RawStep.par.natZero_inv scrutineeStep
        subst scrutineeTargetEq
        subst targetEq
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          by_cases succEq : currentSucc = succTarget
          · subst succEq
            exact (progressStep.2 rfl).elim
          · exact succIH succTarget ⟨succStep, succEq⟩
        · have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩ succTargetIsSN
      · rw [targetEq]
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          exact RawTerm.isStronglyNormalizing.intro currentZero zeroClosure
        · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
      · have succEqZero :
            RawTerm.natSucc predecessorTarget =
              (RawTerm.natZero : RawTerm scope) :=
          RawStep.par.natZero_inv scrutineeStep
        nomatch succEqZero

/-- Typed nat-zero ι SN expansion for `Term.natElim`. -/
theorem Term.natElim_natZero_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw}
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch) :
    Term.isStronglyNormalizing
      (Term.natElim Term.natZero zeroBranch succBranch) :=
  RawTerm.natElim_natZero_isStronglyNormalizing
    zeroIsSN succIsSN

/-- Nat-successor ι SN expansion for `natElim`.

For a canonical successor scrutinee, `natElim` reduces to
`succBranch predecessor`.  The zero branch remains explicit because
congruent reductions may step under it before the ι rule fires. -/
theorem RawTerm.natElim_natSucc_isStronglyNormalizing
    {scope : Nat}
    {predecessor : RawTerm scope}
    (predecessorIsSN : RawTerm.isStronglyNormalizing predecessor) :
    ∀ {zeroBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing zeroBranch →
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.app succBranch predecessor) →
      RawTerm.isStronglyNormalizing
        (RawTerm.natElim
          (RawTerm.natSucc predecessor) zeroBranch succBranch) := by
  induction predecessorIsSN with
  | intro currentPredecessor predecessorClosure predecessorIH =>
    intro zeroBranch zeroIsSN
    induction zeroIsSN with
    | intro currentZero zeroClosure zeroIH =>
      intro succBranch succIsSN succAppIsSN
      induction succIsSN with
      | intro currentSucc succClosure succIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.natElim
            (RawTerm.natSucc currentPredecessor)
            currentZero currentSucc) ?_
        intro target progressStep
        rcases RawStep.par.natElim_inv progressStep.1 with
          ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
            scrutineeStep, zeroStep, succStep⟩
          | ⟨zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
          | ⟨predecessorTarget, succTarget, targetEq,
              scrutineeStep, succStep⟩
        · obtain ⟨predecessorTarget, scrutineeTargetEq,
              predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          subst scrutineeTargetEq
          subst targetEq
          have predecessorTargetIsSN :
              RawTerm.isStronglyNormalizing predecessorTarget := by
            by_cases predecessorEq :
                currentPredecessor = predecessorTarget
            · subst predecessorEq
              exact RawTerm.isStronglyNormalizing.intro
                currentPredecessor predecessorClosure
            · exact predecessorClosure predecessorTarget
                ⟨predecessorStep, predecessorEq⟩
          have zeroTargetIsSN :
              RawTerm.isStronglyNormalizing zeroTarget := by
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              exact RawTerm.isStronglyNormalizing.intro
                currentZero zeroClosure
            · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
          have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          have succAppTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app succTarget predecessorTarget) := by
            by_cases appEq :
                RawTerm.app currentSucc currentPredecessor =
                  RawTerm.app succTarget predecessorTarget
            · rw [← appEq]
              exact succAppIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                succAppIsSN
                ⟨RawStep.par.app succStep predecessorStep, appEq⟩
          by_cases predecessorEq : currentPredecessor = predecessorTarget
          · subst predecessorEq
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              by_cases succEq : currentSucc = succTarget
              · subst succEq
                exact (progressStep.2 rfl).elim
              · exact succIH succTarget ⟨succStep, succEq⟩
                  succAppTargetIsSN
            · exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩
                succTargetIsSN succAppTargetIsSN
          · exact predecessorIH predecessorTarget
              ⟨predecessorStep, predecessorEq⟩
              zeroTargetIsSN succTargetIsSN succAppTargetIsSN
        · obtain ⟨_predecessorTarget, natZeroEq, _predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          nomatch natZeroEq
        · obtain ⟨_predecessorTargetFromScrutinee, successorEq,
              predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          injection successorEq with _scopeEq predecessorTargetEq
          subst targetEq
          have predecessorStepToTarget :
              RawStep.par currentPredecessor predecessorTarget := by
            rw [predecessorTargetEq]
            exact predecessorStep
          have succAppTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app succTarget predecessorTarget) := by
            by_cases appEq :
                RawTerm.app currentSucc currentPredecessor =
                  RawTerm.app succTarget predecessorTarget
            · rw [← appEq]
              exact succAppIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                succAppIsSN
                ⟨RawStep.par.app succStep predecessorStepToTarget, appEq⟩
          exact succAppTargetIsSN

/-- Typed nat-successor ι SN expansion for `Term.natElim`. -/
theorem Term.natElim_natSucc_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    {predecessor : Term context Ty.nat predecessorRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw}
    (predecessorIsSN : Term.isStronglyNormalizing predecessor)
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch)
    (succAppIsSN :
      Term.isStronglyNormalizing
        (Term.app succBranch predecessor)) :
    Term.isStronglyNormalizing
      (Term.natElim
        (Term.natSucc predecessor) zeroBranch succBranch) :=
  RawTerm.natElim_natSucc_isStronglyNormalizing
    predecessorIsSN zeroIsSN succIsSN succAppIsSN

/-- General SN preservation for `natElim`.

The successor branch is supplied through a raw SN closure over every
strongly-normalizing predecessor.  This is the exact information needed
by the deep successor ι arm of `RawStep.par.natElim_inv`, where the
scrutinee may develop to `natSucc predecessor` before the eliminator
fires. -/
theorem RawTerm.natElim_isStronglyNormalizing {scope : Nat}
    {scrutinee : RawTerm scope}
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutinee) :
    ∀ {zeroBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing zeroBranch →
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      (∀ {predecessor : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessor →
        RawTerm.isStronglyNormalizing
          (RawTerm.app succBranch predecessor)) →
      RawTerm.isStronglyNormalizing
        (RawTerm.natElim scrutinee zeroBranch succBranch) := by
  induction scrutineeIsSN with
  | intro currentScrutinee scrutineeClosure scrutineeIH =>
    intro zeroBranch zeroIsSN
    induction zeroIsSN with
    | intro currentZero zeroClosure zeroIH =>
      intro succBranch succIsSN succAppIsSN
      induction succIsSN with
      | intro currentSucc succClosure succIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.natElim currentScrutinee currentZero currentSucc) ?_
        intro target progressStep
        rcases RawStep.par.natElim_inv progressStep.1 with
          ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
            scrutineeStep, zeroStep, succStep⟩
          | ⟨zeroTarget, targetEq, scrutineeStep, zeroStep⟩
          | ⟨predecessorTarget, succTarget, targetEq,
              scrutineeStep, succStep⟩
        · subst targetEq
          have scrutineeTargetIsSN :
              RawTerm.isStronglyNormalizing scrutineeTarget := by
            by_cases scrutineeEq : currentScrutinee = scrutineeTarget
            · subst scrutineeEq
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact scrutineeClosure scrutineeTarget
                ⟨scrutineeStep, scrutineeEq⟩
          have zeroTargetIsSN :
              RawTerm.isStronglyNormalizing zeroTarget := by
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              exact RawTerm.isStronglyNormalizing.intro
                currentZero zeroClosure
            · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
          have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          have succTargetAppIsSN :
              ∀ {predecessor : RawTerm scope},
                RawTerm.isStronglyNormalizing predecessor →
                RawTerm.isStronglyNormalizing
                  (RawTerm.app succTarget predecessor) := by
            intro predecessor predecessorIsSN
            by_cases appEq :
                RawTerm.app currentSucc predecessor =
                  RawTerm.app succTarget predecessor
            · rw [← appEq]
              exact succAppIsSN predecessorIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                (succAppIsSN predecessorIsSN)
                ⟨RawStep.par.app succStep (RawStep.par.refl predecessor),
                  appEq⟩
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              by_cases succEq : currentSucc = succTarget
              · subst succEq
                exact (progressStep.2 rfl).elim
              · exact succIH succTarget ⟨succStep, succEq⟩
                  succTargetAppIsSN
            · exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩
                succTargetIsSN succTargetAppIsSN
          · exact scrutineeIH scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              zeroTargetIsSN succTargetIsSN succTargetAppIsSN
        · rw [targetEq]
          by_cases zeroEq : currentZero = zeroTarget
          · subst zeroEq
            exact RawTerm.isStronglyNormalizing.intro
              currentZero zeroClosure
          · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
        · subst targetEq
          have successorScrutineeIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.natSucc predecessorTarget) := by
            by_cases scrutineeEq :
                currentScrutinee = RawTerm.natSucc predecessorTarget
            · rw [← scrutineeEq]
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact RawTerm.isStronglyNormalizing.step_preserves
                (RawTerm.isStronglyNormalizing.intro
                  currentScrutinee scrutineeClosure)
                ⟨scrutineeStep, scrutineeEq⟩
          have predecessorIsSN :
              RawTerm.isStronglyNormalizing predecessorTarget :=
            RawTerm.natSucc_predecessor_isStronglyNormalizing
              successorScrutineeIsSN
          by_cases appEq :
              RawTerm.app currentSucc predecessorTarget =
                RawTerm.app succTarget predecessorTarget
          · rw [← appEq]
            exact succAppIsSN predecessorIsSN
          · exact RawTerm.isStronglyNormalizing.step_preserves
              (succAppIsSN predecessorIsSN)
              ⟨RawStep.par.app succStep
                (RawStep.par.refl predecessorTarget), appEq⟩

/-- Typed wrapper for general `natElim` SN preservation. -/
theorem Term.natElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch)
    (succAppIsSN :
      ∀ {predecessorRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app succRaw predecessorRaw)) :
    Term.isStronglyNormalizing
      (Term.natElim scrutinee zeroBranch succBranch) :=
  RawTerm.natElim_isStronglyNormalizing
    scrutineeIsSN zeroIsSN succIsSN succAppIsSN

/-- Nat-zero ι SN expansion for `natRec`.

For a canonical zero scrutinee, `natRec` reduces to the zero branch.
The successor branch remains in the statement because congruent
reductions may step under it before the ι rule fires. -/
theorem RawTerm.natRec_natZero_isStronglyNormalizing
    {scope : Nat}
    {zeroBranch : RawTerm scope}
    (zeroIsSN : RawTerm.isStronglyNormalizing zeroBranch) :
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natRec RawTerm.natZero zeroBranch succBranch) := by
  induction zeroIsSN with
  | intro currentZero zeroClosure zeroIH =>
    intro succBranch succIsSN
    induction succIsSN with
    | intro currentSucc succClosure succIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.natRec RawTerm.natZero currentZero currentSucc) ?_
      intro target progressStep
      rcases RawStep.par.natRec_inv progressStep.1 with
        ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
          scrutineeStep, zeroStep, succStep⟩
        | ⟨zeroTarget, targetEq, _scrutineeStep, zeroStep⟩
        | ⟨predecessorTarget, _zeroTarget, _succTarget, _targetEq,
            scrutineeStep, _zeroStep, _succStep⟩
      · have scrutineeTargetEq :
            scrutineeTarget = (RawTerm.natZero : RawTerm scope) :=
          RawStep.par.natZero_inv scrutineeStep
        subst scrutineeTargetEq
        subst targetEq
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          by_cases succEq : currentSucc = succTarget
          · subst succEq
            exact (progressStep.2 rfl).elim
          · exact succIH succTarget ⟨succStep, succEq⟩
        · have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩ succTargetIsSN
      · rw [targetEq]
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          exact RawTerm.isStronglyNormalizing.intro currentZero zeroClosure
        · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
      · have succEqZero :
            RawTerm.natSucc predecessorTarget =
              (RawTerm.natZero : RawTerm scope) :=
          RawStep.par.natZero_inv scrutineeStep
        nomatch succEqZero

/-- Typed nat-zero ι SN expansion for `Term.natRec`. -/
theorem Term.natRec_natZero_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw}
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch) :
    Term.isStronglyNormalizing
      (Term.natRec Term.natZero zeroBranch succBranch) :=
  RawTerm.natRec_natZero_isStronglyNormalizing
    zeroIsSN succIsSN

/-- Nat-successor ι SN expansion for `natRec`.

For a canonical successor scrutinee, `natRec` reduces to
`succBranch predecessor (natRec predecessor zeroBranch succBranch)`.
The recursive call and the full contractum are explicit premises:
this raw lemma only transports SN backward across the ι redex and
congruent reducts. -/
theorem RawTerm.natRec_natSucc_isStronglyNormalizing
    {scope : Nat}
    {predecessor : RawTerm scope}
    (predecessorIsSN : RawTerm.isStronglyNormalizing predecessor) :
    ∀ {zeroBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing zeroBranch →
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natRec predecessor zeroBranch succBranch) →
      RawTerm.isStronglyNormalizing
        (RawTerm.app (RawTerm.app succBranch predecessor)
          (RawTerm.natRec predecessor zeroBranch succBranch)) →
      RawTerm.isStronglyNormalizing
        (RawTerm.natRec
          (RawTerm.natSucc predecessor) zeroBranch succBranch) := by
  induction predecessorIsSN with
  | intro currentPredecessor predecessorClosure predecessorIH =>
    intro zeroBranch zeroIsSN
    induction zeroIsSN with
    | intro currentZero zeroClosure zeroIH =>
      intro succBranch succIsSN recursiveCallIsSN contractumIsSN
      induction succIsSN with
      | intro currentSucc succClosure succIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.natRec
            (RawTerm.natSucc currentPredecessor)
            currentZero currentSucc) ?_
        intro target progressStep
        rcases RawStep.par.natRec_inv progressStep.1 with
          ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
            scrutineeStep, zeroStep, succStep⟩
          | ⟨zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
          | ⟨predecessorTarget, zeroTarget, succTarget, targetEq,
              scrutineeStep, zeroStep, succStep⟩
        · obtain ⟨predecessorTarget, scrutineeTargetEq,
              predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          subst scrutineeTargetEq
          subst targetEq
          have predecessorTargetIsSN :
              RawTerm.isStronglyNormalizing predecessorTarget := by
            by_cases predecessorEq :
                currentPredecessor = predecessorTarget
            · subst predecessorEq
              exact RawTerm.isStronglyNormalizing.intro
                currentPredecessor predecessorClosure
            · exact predecessorClosure predecessorTarget
                ⟨predecessorStep, predecessorEq⟩
          have zeroTargetIsSN :
              RawTerm.isStronglyNormalizing zeroTarget := by
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              exact RawTerm.isStronglyNormalizing.intro
                currentZero zeroClosure
            · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
          have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          have recursiveCallTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.natRec
                  predecessorTarget zeroTarget succTarget) := by
            by_cases recursiveCallEq :
                RawTerm.natRec
                    currentPredecessor currentZero currentSucc =
                  RawTerm.natRec
                    predecessorTarget zeroTarget succTarget
            · rw [← recursiveCallEq]
              exact recursiveCallIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                recursiveCallIsSN
                ⟨RawStep.par.natRec predecessorStep zeroStep succStep,
                  recursiveCallEq⟩
          have contractumTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app (RawTerm.app succTarget predecessorTarget)
                  (RawTerm.natRec
                    predecessorTarget zeroTarget succTarget)) := by
            by_cases contractumEq :
                RawTerm.app
                    (RawTerm.app currentSucc currentPredecessor)
                    (RawTerm.natRec
                      currentPredecessor currentZero currentSucc) =
                  RawTerm.app
                    (RawTerm.app succTarget predecessorTarget)
                    (RawTerm.natRec
                      predecessorTarget zeroTarget succTarget)
            · rw [← contractumEq]
              exact contractumIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                contractumIsSN
                ⟨RawStep.par.app
                    (RawStep.par.app succStep predecessorStep)
                    (RawStep.par.natRec
                      predecessorStep zeroStep succStep),
                  contractumEq⟩
          by_cases predecessorEq : currentPredecessor = predecessorTarget
          · subst predecessorEq
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              by_cases succEq : currentSucc = succTarget
              · subst succEq
                exact (progressStep.2 rfl).elim
              · exact succIH succTarget ⟨succStep, succEq⟩
                  recursiveCallTargetIsSN contractumTargetIsSN
            · exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩
                succTargetIsSN recursiveCallTargetIsSN
                contractumTargetIsSN
          · exact predecessorIH predecessorTarget
              ⟨predecessorStep, predecessorEq⟩
              zeroTargetIsSN succTargetIsSN
              recursiveCallTargetIsSN contractumTargetIsSN
        · obtain ⟨_predecessorTarget, natZeroEq, _predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          nomatch natZeroEq
        · obtain ⟨_predecessorTargetFromScrutinee, successorEq,
              predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          injection successorEq with _scopeEq predecessorTargetEq
          subst targetEq
          have predecessorStepToTarget :
              RawStep.par currentPredecessor predecessorTarget := by
            rw [predecessorTargetEq]
            exact predecessorStep
          have recursiveCallTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.natRec
                  predecessorTarget zeroTarget succTarget) := by
            by_cases recursiveCallEq :
                RawTerm.natRec
                    currentPredecessor currentZero currentSucc =
                  RawTerm.natRec
                    predecessorTarget zeroTarget succTarget
            · rw [← recursiveCallEq]
              exact recursiveCallIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                recursiveCallIsSN
                ⟨RawStep.par.natRec
                    predecessorStepToTarget zeroStep succStep,
                  recursiveCallEq⟩
          have contractumTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app (RawTerm.app succTarget predecessorTarget)
                  (RawTerm.natRec
                    predecessorTarget zeroTarget succTarget)) := by
            by_cases contractumEq :
                RawTerm.app
                    (RawTerm.app currentSucc currentPredecessor)
                    (RawTerm.natRec
                      currentPredecessor currentZero currentSucc) =
                  RawTerm.app
                    (RawTerm.app succTarget predecessorTarget)
                    (RawTerm.natRec
                      predecessorTarget zeroTarget succTarget)
            · rw [← contractumEq]
              exact contractumIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                contractumIsSN
                ⟨RawStep.par.app
                    (RawStep.par.app succStep predecessorStepToTarget)
                    (RawStep.par.natRec
                      predecessorStepToTarget zeroStep succStep),
                  contractumEq⟩
          exact contractumTargetIsSN

/-- Typed nat-successor ι SN expansion for `Term.natRec`. -/
theorem Term.natRec_natSucc_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    {predecessor : Term context Ty.nat predecessorRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw}
    (predecessorIsSN : Term.isStronglyNormalizing predecessor)
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch)
    (recursiveCallIsSN :
      Term.isStronglyNormalizing
        (Term.natRec predecessor zeroBranch succBranch))
    (contractumIsSN :
      Term.isStronglyNormalizing
        (Term.app (Term.app succBranch predecessor)
          (Term.natRec predecessor zeroBranch succBranch))) :
    Term.isStronglyNormalizing
      (Term.natRec
        (Term.natSucc predecessor) zeroBranch succBranch) :=
  RawTerm.natRec_natSucc_isStronglyNormalizing
    predecessorIsSN zeroIsSN succIsSN recursiveCallIsSN contractumIsSN

/-- General SN preservation for `natRec`.

The successor contractum is supplied as an explicit closure over every
strongly-normalizing predecessor and every strongly-normalizing branch
candidate.  This matches the current SN-output endpoint: the theorem
transports normalization through congruent recursor reductions and the
zero/successor ι cases without claiming full recursive Reducible
closure at the motive. -/
theorem RawTerm.natRec_isStronglyNormalizing {scope : Nat}
    {scrutinee : RawTerm scope}
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutinee) :
    ∀ {zeroBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing zeroBranch →
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      (∀ {predecessor zeroTarget succTarget : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessor →
        RawTerm.isStronglyNormalizing zeroTarget →
        RawTerm.isStronglyNormalizing succTarget →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app succTarget predecessor)
            (RawTerm.natRec predecessor zeroTarget succTarget))) →
      RawTerm.isStronglyNormalizing
        (RawTerm.natRec scrutinee zeroBranch succBranch) := by
  induction scrutineeIsSN with
  | intro currentScrutinee scrutineeClosure scrutineeIH =>
    intro zeroBranch zeroIsSN
    induction zeroIsSN with
    | intro currentZero zeroClosure zeroIH =>
      intro succBranch succIsSN contractumClosure
      induction succIsSN with
      | intro currentSucc succClosure succIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.natRec currentScrutinee currentZero currentSucc) ?_
        intro target progressStep
        rcases RawStep.par.natRec_inv progressStep.1 with
          ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
            scrutineeStep, zeroStep, succStep⟩
          | ⟨zeroTarget, targetEq, scrutineeStep, zeroStep⟩
          | ⟨predecessorTarget, zeroTarget, succTarget, targetEq,
              scrutineeStep, zeroStep, succStep⟩
        · subst targetEq
          have scrutineeTargetIsSN :
              RawTerm.isStronglyNormalizing scrutineeTarget := by
            by_cases scrutineeEq : currentScrutinee = scrutineeTarget
            · subst scrutineeEq
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact scrutineeClosure scrutineeTarget
                ⟨scrutineeStep, scrutineeEq⟩
          have zeroTargetIsSN :
              RawTerm.isStronglyNormalizing zeroTarget := by
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              exact RawTerm.isStronglyNormalizing.intro
                currentZero zeroClosure
            · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
          have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              by_cases succEq : currentSucc = succTarget
              · subst succEq
                exact (progressStep.2 rfl).elim
              · exact succIH succTarget ⟨succStep, succEq⟩
            · exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩
                succTargetIsSN contractumClosure
          · exact scrutineeIH scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              zeroTargetIsSN succTargetIsSN contractumClosure
        · rw [targetEq]
          by_cases zeroEq : currentZero = zeroTarget
          · subst zeroEq
            exact RawTerm.isStronglyNormalizing.intro
              currentZero zeroClosure
          · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
        · subst targetEq
          have successorScrutineeIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.natSucc predecessorTarget) := by
            by_cases scrutineeEq :
                currentScrutinee = RawTerm.natSucc predecessorTarget
            · rw [← scrutineeEq]
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact RawTerm.isStronglyNormalizing.step_preserves
                (RawTerm.isStronglyNormalizing.intro
                  currentScrutinee scrutineeClosure)
                ⟨scrutineeStep, scrutineeEq⟩
          have predecessorIsSN :
              RawTerm.isStronglyNormalizing predecessorTarget :=
            RawTerm.natSucc_predecessor_isStronglyNormalizing
              successorScrutineeIsSN
          have zeroTargetIsSN :
              RawTerm.isStronglyNormalizing zeroTarget := by
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              exact RawTerm.isStronglyNormalizing.intro
                currentZero zeroClosure
            · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
          have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          exact contractumClosure
            predecessorIsSN zeroTargetIsSN succTargetIsSN

/-- Typed wrapper for general `natRec` SN preservation. -/
theorem Term.natRec_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch)
    (contractumIsSN :
      ∀ {predecessorRaw zeroTargetRaw succTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing zeroTargetRaw →
        RawTerm.isStronglyNormalizing succTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app succTargetRaw predecessorRaw)
            (RawTerm.natRec
              predecessorRaw zeroTargetRaw succTargetRaw))) :
    Term.isStronglyNormalizing
      (Term.natRec scrutinee zeroBranch succBranch) :=
  RawTerm.natRec_isStronglyNormalizing
    scrutineeIsSN zeroIsSN succIsSN contractumIsSN

/-- **K12.20.W optionSome SN preservation**.  Sister to
`natSucc_isStronglyNormalizing` — unary cong-only ctor with
`optionSome_inv` for step inversion + `RawTerm.optionSome`
injectivity for the parProgress disequality. -/
theorem RawTerm.optionSome_isStronglyNormalizing {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.optionSome valueTerm) := by
  induction valueIsSN with
  | intro currentValue _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.optionSome currentValue) ?_
    intro target progressStep
    obtain ⟨valueTarget, targetEq, valueStep⟩ :=
      RawStep.par.optionSome_inv progressStep.1
    subst targetEq
    have valueDistinct :
        currentValue ≠ valueTarget := fun valueEq =>
      progressStep.2 (congrArg RawTerm.optionSome valueEq)
    exact inductiveHypothesis valueTarget
      ⟨valueStep, valueDistinct⟩

/-- Option-some ι SN expansion for the eliminator.

The option candidate stores the eliminator result as an SN-output
closure.  For the canonical `Some` branch, the ι target is
`app someBranch value`; this lemma lifts SN of that target through
all congruent reductions of the scrutinee and branches. -/
theorem RawTerm.optionMatch_optionSome_isStronglyNormalizing
    {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    ∀ {noneBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing noneBranch →
    ∀ {someBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing someBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.app someBranch valueTerm) →
      RawTerm.isStronglyNormalizing
        (RawTerm.optionMatch
          (RawTerm.optionSome valueTerm) noneBranch someBranch) := by
  induction valueIsSN with
  | intro currentValue valueClosure valueIH =>
    intro noneBranch noneIsSN
    induction noneIsSN with
    | intro currentNone noneClosure noneIH =>
      intro someBranch someIsSN someAppIsSN
      induction someIsSN with
      | intro currentSome someClosure someIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.optionMatch
            (RawTerm.optionSome currentValue) currentNone currentSome) ?_
        intro target progressStep
        rcases RawStep.par.optionMatch_inv progressStep.1 with
          ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
            scrutineeStep, noneStep, someStep⟩
          | ⟨noneTarget, targetEq, scrutineeStep, noneStep⟩
          | ⟨valueTarget, someTarget, targetEq, scrutineeStep, someStep⟩
        · obtain ⟨valueTarget, scrutineeTargetEq, valueStep⟩ :=
            RawStep.par.optionSome_inv scrutineeStep
          subst scrutineeTargetEq
          subst targetEq
          by_cases valueEq : currentValue = valueTarget
          · subst valueEq
            by_cases noneEq : currentNone = noneTarget
            · subst noneEq
              by_cases someEq : currentSome = someTarget
              · subst someEq
                exact (progressStep.2 rfl).elim
              · have someAppTargetIsSN :
                    RawTerm.isStronglyNormalizing
                      (RawTerm.app someTarget currentValue) := by
                  by_cases appEq :
                      RawTerm.app currentSome currentValue =
                        RawTerm.app someTarget currentValue
                  · rw [← appEq]
                    exact someAppIsSN
                  · exact RawTerm.isStronglyNormalizing.step_preserves
                      someAppIsSN
                      ⟨RawStep.par.app someStep
                        (RawStep.par.refl currentValue), appEq⟩
                exact someIH someTarget ⟨someStep, someEq⟩
                  someAppTargetIsSN
            · have someTargetIsSN :
                  RawTerm.isStronglyNormalizing someTarget := by
                by_cases someEq : currentSome = someTarget
                · subst someEq
                  exact RawTerm.isStronglyNormalizing.intro
                    currentSome someClosure
                · exact someClosure someTarget ⟨someStep, someEq⟩
              have someAppTargetIsSN :
                  RawTerm.isStronglyNormalizing
                    (RawTerm.app someTarget currentValue) := by
                by_cases appEq :
                    RawTerm.app currentSome currentValue =
                      RawTerm.app someTarget currentValue
                · rw [← appEq]
                  exact someAppIsSN
                · exact RawTerm.isStronglyNormalizing.step_preserves
                    someAppIsSN
                    ⟨RawStep.par.app someStep
                      (RawStep.par.refl currentValue), appEq⟩
              exact noneIH noneTarget ⟨noneStep, noneEq⟩
                someTargetIsSN someAppTargetIsSN
          · have noneTargetIsSN :
                RawTerm.isStronglyNormalizing noneTarget := by
              by_cases noneEq : currentNone = noneTarget
              · subst noneEq
                exact RawTerm.isStronglyNormalizing.intro
                  currentNone noneClosure
              · exact noneClosure noneTarget ⟨noneStep, noneEq⟩
            have someTargetIsSN :
                RawTerm.isStronglyNormalizing someTarget := by
              by_cases someEq : currentSome = someTarget
              · subst someEq
                exact RawTerm.isStronglyNormalizing.intro
                  currentSome someClosure
              · exact someClosure someTarget ⟨someStep, someEq⟩
            have someAppTargetIsSN :
                RawTerm.isStronglyNormalizing
                  (RawTerm.app someTarget valueTarget) := by
              by_cases appEq :
                  RawTerm.app currentSome currentValue =
                    RawTerm.app someTarget valueTarget
              · rw [← appEq]
                exact someAppIsSN
              · exact RawTerm.isStronglyNormalizing.step_preserves
                  someAppIsSN
                  ⟨RawStep.par.app someStep valueStep, appEq⟩
            exact valueIH valueTarget ⟨valueStep, valueEq⟩
              noneTargetIsSN someTargetIsSN someAppTargetIsSN
        · obtain ⟨valueTarget, optionSomeEq, _valueStep⟩ :=
            RawStep.par.optionSome_inv scrutineeStep
          nomatch optionSomeEq
        · obtain ⟨valueTargetFromScrutinee, optionSomeEq, valueStep⟩ :=
            RawStep.par.optionSome_inv scrutineeStep
          injection optionSomeEq with _scopeEq valueTargetEq
          subst targetEq
          have valueStepToTarget :
              RawStep.par currentValue valueTarget := by
            rw [valueTargetEq]
            exact valueStep
          have someAppTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app someTarget valueTarget) := by
            by_cases appEq :
                RawTerm.app currentSome currentValue =
                  RawTerm.app someTarget valueTarget
            · rw [← appEq]
              exact someAppIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                someAppIsSN
                ⟨RawStep.par.app someStep valueStepToTarget, appEq⟩
          exact someAppTargetIsSN

/-- Typed option-some ι SN expansion for `Term.optionMatch`. -/
theorem Term.optionMatch_optionSome_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {valueRaw noneRaw someRaw : RawTerm scope}
    {valueTerm : Term context elementType valueRaw}
    {noneBranch : Term context motiveType noneRaw}
    {someBranch : Term context (Ty.arrow elementType motiveType) someRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm)
    (noneIsSN : Term.isStronglyNormalizing noneBranch)
    (someIsSN : Term.isStronglyNormalizing someBranch)
    (someAppIsSN :
      Term.isStronglyNormalizing (Term.app someBranch valueTerm)) :
    Term.isStronglyNormalizing
      (Term.optionMatch (Term.optionSome valueTerm) noneBranch someBranch) :=
  RawTerm.optionMatch_optionSome_isStronglyNormalizing
    valueIsSN noneIsSN someIsSN someAppIsSN


end LeanFX2
