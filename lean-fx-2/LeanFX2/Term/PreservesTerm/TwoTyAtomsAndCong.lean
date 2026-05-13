import LeanFX2.Term.PreservesTerm.TierZeroAndUnary
import LeanFX2.Term.PreservesTerm.TierTwoBinary
import LeanFX2.Term.PreservesTerm.EliminatorConstantMotive

/-! # LeanFX2.Term.PreservesTerm.TwoTyAtomsAndCong

Tier 0/1/2 lifts re-expressed at the two-Ty existential so that
Term-induction-driven assembly of the headline can quantify the
target Ty alongside the target Term.  Each lift wraps the
fixed-Ty companion from `TierZeroAndUnary` / `TierTwoBinary`.

Covers 31 ctors: unit, boolTrue, boolFalse, natZero, var, listNil,
optionNone, interval0, interval1; natSucc, optionSome, eitherInl,
eitherInr, intervalOpp, modIntro, subsume, recordIntro, lam,
lamPi, pathLam, sessionRecv, universeCode, cumulUp;
intervalMeet, intervalJoin, glueIntro, hcomp, codataUnfold,
sessionSend, listCons, equivApp, refineIntro, effectPerform.

## Root status

Zero-axiom; carved from `Term/PreservesTerm.lean`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}


/-! ## Tier 0/1/2/3 lifts re-expressed at two-Ty existential

The existing fixed-Ty lifts (lift_unit, lift_lam, ..., lift_codataDest)
all produce targets at a SPECIFIC type.  When assembled into the
headline `Term.preserves` via Term induction, we want a uniform IH
shape: `∃ targetTy targetTerm, Step.par sourceTerm targetTerm`.

These wrapper theorems thread the existing fixed-Ty lift's result
through the two-Ty existential.  Each wrapper is a 1-line
`⟨_, target, step⟩` rebracketing.

When all 75 ctors have either a `_full` or `_uniform` lift, the
headline can dispatch via Term induction.  The ctors blocked by the
walls (refl/funextRefl/etc; pair; appPi; transp full) cannot be
rebracketed since their underlying lifts don't exist. -/

/-- **Tier 0 — Term.unit at two-Ty.** -/
theorem RawStep.par.lift_full_unit
    (sourceTerm : Term context Ty.unit (RawTerm.unit : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.unit : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_unit sourceTerm rawStep
  exact ⟨Ty.unit, target, step⟩

/-- **Tier 0 — Term.boolTrue at two-Ty.** -/
theorem RawStep.par.lift_full_boolTrue
    (sourceTerm : Term context Ty.bool (RawTerm.boolTrue : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.boolTrue : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_boolTrue sourceTerm rawStep
  exact ⟨Ty.bool, target, step⟩

/-- **Tier 0 — Term.boolFalse at two-Ty.** -/
theorem RawStep.par.lift_full_boolFalse
    (sourceTerm : Term context Ty.bool (RawTerm.boolFalse : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.boolFalse : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_boolFalse sourceTerm rawStep
  exact ⟨Ty.bool, target, step⟩

/-- **Tier 0 — Term.natZero at two-Ty.** -/
theorem RawStep.par.lift_full_natZero
    (sourceTerm : Term context Ty.nat (RawTerm.natZero : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.natZero : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_natZero sourceTerm rawStep
  exact ⟨Ty.nat, target, step⟩

/-- **Tier 0 — Term.var at two-Ty.** -/
theorem RawStep.par.lift_full_var
    {sourceType : Ty level scope} {position : Fin scope}
    (sourceTerm : Term context sourceType (RawTerm.var position))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.var position) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_var sourceTerm rawStep
  exact ⟨sourceType, target, step⟩

/-- **Tier 0 — Term.listNil at two-Ty.** -/
theorem RawStep.par.lift_full_listNil
    {elementType : Ty level scope}
    (sourceTerm :
      Term context (Ty.listType elementType) (RawTerm.listNil : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.listNil : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_listNil sourceTerm rawStep
  exact ⟨Ty.listType elementType, target, step⟩

/-- **Tier 0 — Term.optionNone at two-Ty.** -/
theorem RawStep.par.lift_full_optionNone
    {elementType : Ty level scope}
    (sourceTerm :
      Term context (Ty.optionType elementType) (RawTerm.optionNone : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.optionNone : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_optionNone sourceTerm rawStep
  exact ⟨Ty.optionType elementType, target, step⟩

/-- **Tier 0 — Term.interval0 at two-Ty.** -/
theorem RawStep.par.lift_full_interval0
    (sourceTerm : Term context Ty.interval (RawTerm.interval0 : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.interval0 : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_interval0 sourceTerm rawStep
  exact ⟨Ty.interval, target, step⟩

/-- **Tier 0 — Term.interval1 at two-Ty.** -/
theorem RawStep.par.lift_full_interval1
    (sourceTerm : Term context Ty.interval (RawTerm.interval1 : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.interval1 : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_interval1 sourceTerm rawStep
  exact ⟨Ty.interval, target, step⟩

/-- **Tier 1 — Term.natSucc at two-Ty.** -/
theorem RawStep.par.lift_full_natSucc
    {predRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predRaw)
    (predLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par predRaw targetRawIH →
      ∃ predTarget : Term context Ty.nat targetRawIH,
        Step.par predecessor predTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.natSucc predRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.natSucc predecessor) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_natSucc predecessor predLift rawStep
  exact ⟨Ty.nat, target, step⟩

/-- **Tier 1 — Term.optionSome at two-Ty.** -/
theorem RawStep.par.lift_full_optionSome
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context elementType targetRawIH,
        Step.par valueTerm valueTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.optionSome valueRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.optionSome valueTerm) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_optionSome valueTerm valueLift rawStep
  exact ⟨Ty.optionType elementType, target, step⟩

/-- **Tier 1 — Term.eitherInl at two-Ty.** -/
theorem RawStep.par.lift_full_eitherInl
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context leftType targetRawIH,
        Step.par valueTerm valueTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.eitherInl valueRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.eitherInl (rightType := rightType) valueTerm) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_eitherInl (rightType := rightType) valueTerm valueLift rawStep
  exact ⟨Ty.eitherType leftType rightType, target, step⟩

/-- **Tier 1 — Term.eitherInr at two-Ty.** -/
theorem RawStep.par.lift_full_eitherInr
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context rightType targetRawIH,
        Step.par valueTerm valueTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.eitherInr valueRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.eitherInr (leftType := leftType) valueTerm) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_eitherInr (leftType := leftType) valueTerm valueLift rawStep
  exact ⟨Ty.eitherType leftType rightType, target, step⟩

/-- **Tier 1 — Term.intervalOpp at two-Ty.** -/
theorem RawStep.par.lift_full_intervalOpp
    {innerRaw : RawTerm scope}
    (innerValue : Term context Ty.interval innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context Ty.interval targetRawIH,
        Step.par innerValue innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.intervalOpp innerRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.intervalOpp innerValue) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_intervalOpp innerValue innerLift rawStep
  exact ⟨Ty.interval, target, step⟩

/-- **Tier 1 — Term.modIntro at two-Ty.** -/
theorem RawStep.par.lift_full_modIntro
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.modIntro innerRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.modIntro innerTerm) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_modIntro innerTerm innerLift rawStep
  exact ⟨innerType, target, step⟩

/-- **Tier 1 — Term.subsume at two-Ty.** -/
theorem RawStep.par.lift_full_subsume
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.subsume innerRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.subsume innerTerm) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_subsume innerTerm innerLift rawStep
  exact ⟨innerType, target, step⟩

/-- **Tier 1 — Term.recordIntro at two-Ty.** -/
theorem RawStep.par.lift_full_recordIntro
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (firstField : Term context singleFieldType firstRaw)
    (firstLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par firstRaw targetRawIH →
      ∃ firstTarget : Term context singleFieldType targetRawIH,
        Step.par firstField firstTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.recordIntro firstRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.recordIntro firstField) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_recordIntro firstField firstLift rawStep
  exact ⟨Ty.record singleFieldType, target, step⟩

/-- **Tier 1 — Term.lam at two-Ty.** -/
theorem RawStep.par.lift_full_lam
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType.weaken bodyRaw)
    (bodyLift : ∀ {targetRawIH : RawTerm (scope + 1)},
      RawStep.par bodyRaw targetRawIH →
      ∃ bodyTarget : Term (context.cons domainType) codomainType.weaken targetRawIH,
        Step.par body bodyTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.lam bodyRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.lam (codomainType := codomainType) body) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_lam body bodyLift rawStep
  exact ⟨Ty.arrow domainType codomainType, target, step⟩

/-- **Tier 1 — Term.lamPi at two-Ty.** -/
theorem RawStep.par.lift_full_lamPi
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType bodyRaw)
    (bodyLift : ∀ {targetRawIH : RawTerm (scope + 1)},
      RawStep.par bodyRaw targetRawIH →
      ∃ bodyTarget : Term (context.cons domainType) codomainType targetRawIH,
        Step.par body bodyTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.lam bodyRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.lamPi (domainType := domainType) body) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_lamPi body bodyLift rawStep
  exact ⟨Ty.piTy domainType codomainType, target, step⟩

/-- **Tier 1 — Term.pathLam at two-Ty.** -/
theorem RawStep.par.lift_full_pathLam
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyLift : ∀ {targetRawIH : RawTerm (scope + 1)},
      RawStep.par bodyRaw targetRawIH →
      ∃ bodyTarget :
          Term (context.cons Ty.interval) carrierType.weaken targetRawIH,
        Step.par body bodyTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.pathLam bodyRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint body)
        targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
                             body bodyLift rawStep
  exact ⟨Ty.path carrierType leftEndpoint rightEndpoint, target, step⟩

/-- **Tier 1 — Term.sessionRecv at two-Ty.** -/
theorem RawStep.par.lift_full_sessionRecv
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (channelLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par channelRaw targetRawIH →
      ∃ channelTarget : Term context (Ty.session protocolStep) targetRawIH,
        Step.par channel channelTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.sessionRecv channelRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.sessionRecv channel) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_sessionRecv channel channelLift rawStep
  exact ⟨Ty.session protocolStep, target, step⟩

/-- **Tier 1 — Term.universeCode at two-Ty.** -/
theorem RawStep.par.lift_full_universeCode
    {sourceType : Ty level scope} {innerLevelNat : Nat}
    (sourceTerm :
      Term context sourceType (RawTerm.universeCode innerLevelNat))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.universeCode innerLevelNat : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_universeCode sourceTerm rawStep
  exact ⟨sourceType, target, step⟩

/-- **Tier 1 — Term.cumulUp at two-Ty.** -/
theorem RawStep.par.lift_full_cumulUp
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode : Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (typeCodeLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par codeRaw targetRawIH →
      ∃ typeCodeTarget :
          Term context (Ty.universe lowerLevel levelLeLow) targetRawIH,
        Step.par typeCode typeCodeTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.cumulUpMarker codeRaw : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.cumulUp lowerLevel higherLevel cumulMonotone
                      levelLeLow levelLeHigh typeCode)
        targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_cumulUp lowerLevel higherLevel cumulMonotone
                             levelLeLow levelLeHigh typeCode typeCodeLift rawStep
  exact ⟨Ty.universe higherLevel levelLeHigh, target, step⟩

/-- **Tier 2 — Term.intervalMeet at two-Ty.** -/
theorem RawStep.par.lift_full_intervalMeet
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw)
    (leftLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par leftRaw targetRawIH →
      ∃ leftTarget : Term context Ty.interval targetRawIH,
        Step.par leftValue leftTarget)
    (rightLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par rightRaw targetRawIH →
      ∃ rightTarget : Term context Ty.interval targetRawIH,
        Step.par rightValue rightTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.intervalMeet leftRaw rightRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.intervalMeet leftValue rightValue) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_intervalMeet leftValue rightValue leftLift rightLift rawStep
  exact ⟨Ty.interval, target, step⟩

/-- **Tier 2 — Term.intervalJoin at two-Ty.** -/
theorem RawStep.par.lift_full_intervalJoin
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw)
    (leftLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par leftRaw targetRawIH →
      ∃ leftTarget : Term context Ty.interval targetRawIH,
        Step.par leftValue leftTarget)
    (rightLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par rightRaw targetRawIH →
      ∃ rightTarget : Term context Ty.interval targetRawIH,
        Step.par rightValue rightTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.intervalJoin leftRaw rightRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.intervalJoin leftValue rightValue) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_intervalJoin leftValue rightValue leftLift rightLift rawStep
  exact ⟨Ty.interval, target, step⟩

/-- **Tier 2 — Term.glueIntro at two-Ty.** -/
theorem RawStep.par.lift_full_glueIntro
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context baseType targetRawIH,
        Step.par baseValue baseTarget)
    (partialLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par partialRaw targetRawIH →
      ∃ partialTarget : Term context baseType targetRawIH,
        Step.par partialValue partialTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.glueIntro baseRaw partialRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness baseValue
                        partialValue)
        targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_glueIntro modeIsUnivalent baseType boundaryWitness
                               baseValue partialValue baseLift partialLift rawStep
  exact ⟨Ty.glue baseType boundaryWitness, target, step⟩

/-- **Tier 2 — Term.hcomp at two-Ty.** -/
theorem RawStep.par.lift_full_hcomp
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    (sidesValue : Term context carrierType sidesRaw)
    (capValue : Term context carrierType capRaw)
    (sidesLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par sidesRaw targetRawIH →
      ∃ sidesTarget : Term context carrierType targetRawIH,
        Step.par sidesValue sidesTarget)
    (capLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par capRaw targetRawIH →
      ∃ capTarget : Term context carrierType targetRawIH,
        Step.par capValue capTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.hcomp sidesRaw capRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.hcomp modeIsUnivalent sidesValue capValue) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_hcomp modeIsUnivalent sidesValue capValue sidesLift capLift
                           rawStep
  exact ⟨carrierType, target, step⟩

/-- **Tier 2 — Term.codataUnfold at two-Ty.** -/
theorem RawStep.par.lift_full_codataUnfold
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw)
    (stateLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par stateRaw targetRawIH →
      ∃ stateTarget : Term context stateType targetRawIH,
        Step.par initialState stateTarget)
    (transitionLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par transitionRaw targetRawIH →
      ∃ transitionTarget :
          Term context (Ty.arrow stateType outputType) targetRawIH,
        Step.par transition transitionTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.codataUnfold stateRaw transitionRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.codataUnfold initialState transition) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_codataUnfold initialState transition stateLift transitionLift
                                  rawStep
  exact ⟨Ty.codata stateType outputType, target, step⟩

/-- **Tier 2 — Term.sessionSend at two-Ty.** -/
theorem RawStep.par.lift_full_sessionSend
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (payload : Term context payloadType payloadRaw)
    (channelLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par channelRaw targetRawIH →
      ∃ channelTarget : Term context (Ty.session protocolStep) targetRawIH,
        Step.par channel channelTarget)
    (payloadLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par payloadRaw targetRawIH →
      ∃ payloadTarget : Term context payloadType targetRawIH,
        Step.par payload payloadTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.sessionSend channelRaw payloadRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.sessionSend protocolStep channel payload) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_sessionSend protocolStep channel payload channelLift
                                 payloadLift rawStep
  exact ⟨Ty.session protocolStep, target, step⟩

/-- **Tier 2 — Term.listCons at two-Ty.** -/
theorem RawStep.par.lift_full_listCons
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (headLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par headRaw targetRawIH →
      ∃ headTarget : Term context elementType targetRawIH,
        Step.par headTerm headTarget)
    (tailLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par tailRaw targetRawIH →
      ∃ tailTarget : Term context (Ty.listType elementType) targetRawIH,
        Step.par tailTerm tailTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.listCons headRaw tailRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.listCons headTerm tailTerm) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_listCons headTerm tailTerm headLift tailLift rawStep
  exact ⟨Ty.listType elementType, target, step⟩

/-- **Tier 2 — Term.equivApp at two-Ty.** -/
theorem RawStep.par.lift_full_equivApp
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw)
    (equivLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par equivRaw targetRawIH →
      ∃ equivTarget : Term context (Ty.equiv carrierA carrierB) targetRawIH,
        Step.par equivTerm equivTarget)
    (argumentLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentRaw targetRawIH →
      ∃ argumentTarget : Term context carrierA targetRawIH,
        Step.par argumentTerm argumentTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.equivApp equivRaw argumentRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.equivApp equivTerm argumentTerm) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_equivApp equivTerm argumentTerm equivLift argumentLift rawStep
  exact ⟨carrierB, target, step⟩

/-- **Tier 2 — Term.refineIntro at two-Ty.** -/
theorem RawStep.par.lift_full_refineIntro
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context baseType targetRawIH,
        Step.par baseValue valueTarget)
    (proofLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par proofRaw targetRawIH →
      ∃ proofTarget : Term context Ty.unit targetRawIH,
        Step.par predicateProof proofTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.refineIntro valueRaw proofRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.refineIntro predicate baseValue predicateProof) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_refineIntro predicate baseValue predicateProof valueLift
                                 proofLift rawStep
  exact ⟨Ty.refine baseType predicate, target, step⟩

/-- **Tier 2 — Term.effectPerform at two-Ty.** -/
theorem RawStep.par.lift_full_effectPerform
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    (operationTag :
      Term context (Ty.effect operationSignature.argumentCarrier effectTag)
                   operationRaw)
    (arguments :
      Term context operationSignature.argumentCarrier argumentsRaw)
    (operationLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par operationRaw targetRawIH →
      ∃ operationTarget :
          Term context (Ty.effect operationSignature.argumentCarrier effectTag)
                       targetRawIH,
        Step.par operationTag operationTarget)
    (argumentsLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentsRaw targetRawIH →
      ∃ argumentsTarget :
          Term context operationSignature.argumentCarrier targetRawIH,
        Step.par arguments argumentsTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.effectPerform operationRaw argumentsRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTag arguments)
        targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_effectPerform effectTag effectRow operationSignature
                                   canPerformOperation operationTag arguments
                                   operationLift argumentsLift rawStep
  exact ⟨Ty.effect operationSignature.resultCarrier effectTag, target, step⟩

end LeanFX2
