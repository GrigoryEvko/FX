import LeanFX2.Term.PreservesTerm.EliminatorShallowBeta
import LeanFX2.Term.PreservesTerm.InlineDestructors

/-! # LeanFX2.Term.PreservesTerm.BetaCastWallDemolition

Full lifts for ctors whose β-firing produces target Terms at
substituted types (`codomain.weaken.subst0 ...`).  The fixed-target-Ty
existential cannot satisfy this; these lifts use a two-Ty
existential where the target Ty is itself part of the witness.

Covers 2 full β-cast-wall lifts in this slice: app, pathApp;
plus their helper destructors pathLamDestruct, reflDestruct,
idReflDestruct.

## Root status

Zero-axiom; carved from `Term/PreservesTerm.lean`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}


/-! ## β cast wall demolition — full lifts via two-Ty existential

The fixed-target-Ty existential used by `lift_app_cong`,
`lift_appPi_cong`, `lift_pathApp_cong`, `lift_transp_cong` cannot
absorb the β arms of `app`, `appPi`, `pathApp`, `transp` because the
target Term's Ty index is `codomainType.weaken.subst0 substituent
argRaw` — propositionally equal to `codomainType` via
`Ty.weaken_subst_singleton`, but the `▸` cast propagates through the
existential's other Ty indices.

The fix: generalize the headline existential over the target Ty.
`Step.par`'s native two-Ty signature `{sourceType targetType : Ty
level scope}` accommodates this directly.

```
∃ (targetTy : Ty level scope) (targetTerm : Term context targetTy targetRaw),
  Step.par sourceTerm targetTerm
```

Each `lift_full_<ctor>` lemma uses this two-Ty existential and
absorbs both the cong arm and any β/ι arms uniformly.  When
assembled into the headline `Term.preserves`, the IH has the same
two-Ty shape, and child lifts are typed at the two-Ty existential
form. -/

/-- **β cast wall demolition — Term.app full lift.**  Two-Ty
existential absorbs both the cong arm (target at `codomainType`) and
the β-deep arm (target at `codomainType.weaken.subst0 ...` via
`Term.subst0`).  The function IH stays at fixed `Ty.arrow domainType
codomainType` — the function's type is invariant under reduction at
arrow type.  The argument IH stays at fixed `domainType`. -/
theorem RawStep.par.lift_full_app
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw)
    (functionLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par functionRaw targetRawIH →
      ∃ functionTarget :
          Term context (Ty.arrow domainType codomainType) targetRawIH,
        Step.par functionTerm functionTarget)
    (argumentLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentRaw targetRawIH →
      ∃ argumentTarget : Term context domainType targetRawIH,
        Step.par argumentTerm argumentTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.app functionRaw argumentRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.app functionTerm argumentTerm) targetTerm := by
  rcases RawStep.par.app_inv rawStep with
    ⟨functionTargetRaw, argumentTargetRaw, eq, functionStep, argumentStep⟩
    | ⟨bodyTargetRaw, argumentTargetRaw, eq, functionToLam, argumentStep⟩
  · -- cong arm
    obtain ⟨functionTarget, functionStepTyped⟩ := functionLift functionStep
    obtain ⟨argumentTarget, argumentStepTyped⟩ := argumentLift argumentStep
    cases eq
    exact ⟨codomainType, Term.app functionTarget argumentTarget,
           Step.par.app functionStepTyped argumentStepTyped⟩
  · -- β-deep arm: function raw-reduces to lam bodyTargetRaw
    obtain ⟨functionCanonical, functionStepTyped⟩ := functionLift functionToLam
    obtain ⟨argumentTarget, argumentStepTyped⟩ := argumentLift argumentStep
    -- functionCanonical : Term ctx (Ty.arrow domainType codomainType) (RawTerm.lam bodyTargetRaw)
    -- Use lamDestruct to extract the body
    obtain ⟨bodyTerm, bodyHeq⟩ := Term.lamDestruct functionCanonical
    have bodyEq : functionCanonical = Term.lam (codomainType := codomainType) bodyTerm :=
      eq_of_heq bodyHeq
    rw [bodyEq] at functionStepTyped
    cases eq
    refine ⟨codomainType.weaken.subst0 domainType argumentTargetRaw,
            Term.subst0 bodyTerm argumentTarget, ?_⟩
    exact Step.par.betaAppDeep
            (functionRawSource := bodyTargetRaw)
            functionStepTyped argumentStepTyped

/-- Destructor for `Term.pathLam`.  `RawTerm.pathLam bodyRaw` is
produced uniquely by `Term.pathLam`. -/
def Term.pathLamDestruct
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRaw : RawTerm (scope + 1)}
    (someTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
                   (RawTerm.pathLam bodyRaw)) :
    Σ' (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw),
       HEq someTerm
            (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
                          body) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.pathLam bodyRaw)),
        someType = Ty.path carrierType leftEndpoint rightEndpoint →
        Σ' (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw),
           HEq genericTerm
                (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
                              body) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsPath
  cases genericTerm
  rename_i innerMode innerCarrier innerLeft innerRight body
  have pathEq := Ty.path.inj someTypeIsPath
  cases pathEq.1
  cases pathEq.2.1
  cases pathEq.2.2
  exact ⟨body, HEq.rfl⟩

/-- **β cast wall demolition — Term.pathApp full lift.**  Two-Ty
existential absorbs both the cong arm (target at `carrierType`) and
the β-deep arm (target via `Term.subst0` at `carrierType.weaken.subst0
Ty.interval intervalTargetRaw`).  Per pathApp_inv, both betaPathApp
and betaPathReflApp arms route through the "path develops to pathLam"
disjunct, so we need only handle cong + pathLam-shape β. -/
theorem RawStep.par.lift_full_pathApp
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    (pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term context Ty.interval intervalRaw)
    (pathLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pathRaw targetRawIH →
      ∃ pathTarget :
          Term context (Ty.path carrierType leftEndpoint rightEndpoint) targetRawIH,
        Step.par pathTerm pathTarget)
    (intervalLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par intervalRaw targetRawIH →
      ∃ intervalTarget : Term context Ty.interval targetRawIH,
        Step.par intervalTerm intervalTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.pathApp pathRaw intervalRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.pathApp modeIsUnivalent pathTerm intervalTerm) targetTerm := by
  rcases RawStep.par.pathApp_inv rawStep with
    ⟨pathTargetRaw, intervalTargetRaw, eq, pathStep, intervalStep⟩
    | ⟨bodyTargetRaw, intervalTargetRaw, eq, pathToLam, intervalStep⟩
  · -- cong arm
    obtain ⟨pathTarget, pathStepTyped⟩ := pathLift pathStep
    obtain ⟨intervalTarget, intervalStepTyped⟩ := intervalLift intervalStep
    cases eq
    refine ⟨carrierType, Term.pathApp modeIsUnivalent pathTarget intervalTarget, ?_⟩
    exact Step.par.pathApp modeIsUnivalent pathStepTyped intervalStepTyped
  · -- β-deep arm: path raw-reduces to pathLam bodyTargetRaw
    obtain ⟨pathCanonical, pathStepTyped⟩ := pathLift pathToLam
    obtain ⟨intervalTarget, intervalStepTyped⟩ := intervalLift intervalStep
    -- pathCanonical : Term ctx (Ty.path ...) (RawTerm.pathLam bodyTargetRaw)
    obtain ⟨bodyTerm, bodyHeq⟩ :=
      Term.pathLamDestruct modeIsUnivalent carrierType leftEndpoint rightEndpoint
                           pathCanonical
    have bodyEq :
        pathCanonical =
          Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
                       bodyTerm :=
      eq_of_heq bodyHeq
    rw [bodyEq] at pathStepTyped
    cases eq
    refine ⟨carrierType.weaken.subst0 Ty.interval intervalTargetRaw,
            Term.subst0 bodyTerm intervalTarget, ?_⟩
    exact Step.par.betaPathAppDeep modeIsUnivalent
            (pathSource := pathTerm) (bodyTarget := bodyTerm)
            pathStepTyped intervalStepTyped

/-- Destructor for `Term.refl` at fixed `Ty.id carrier endpoint endpoint`.
Extracts an `Eq` between the witness raw and the endpoint, since
`Term.refl c w : Ty.id c w w` forces both endpoints = w. -/
def Term.reflDestruct
    {carrier : Ty level scope}
    {endpoint : RawTerm scope}
    {rawWitness : RawTerm scope}
    (someTerm :
      Term context (Ty.id carrier endpoint endpoint) (RawTerm.refl rawWitness)) :
    PLift (rawWitness = endpoint) := by
  -- Term.refl forces both endpoints equal to its rawWitness arg, so
  -- having the type say endpoint endpoint and the raw say rawWitness,
  -- we get rawWitness = endpoint by ctor inversion.
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.refl rawWitness)),
        someType = Ty.id carrier endpoint endpoint →
        PLift (rawWitness = endpoint) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsIdRefl
  cases genericTerm
  rename_i innerCarrier
  -- innerCarrier : Ty level scope; the ctor's type is
  --   Ty.id innerCarrier rawWitness rawWitness
  -- which equals (per someTypeIsIdRefl) Ty.id carrier endpoint endpoint.
  have idEq := Ty.id.inj someTypeIsIdRefl
  -- idEq.2.1 : rawWitness = endpoint (left endpoint match)
  exact ⟨idEq.2.1⟩

/-- Destructor for `Term.refl` at type `Ty.id carrier leftEndpoint
rightEndpoint` with raw `RawTerm.refl witnessRaw`.  Forces leftEndpoint
= rightEndpoint = witnessRaw and yields HEq alignment. -/
def Term.idReflDestruct
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint)
                   (RawTerm.refl witnessRaw)) :
    Σ' (_witnessEqLeft : witnessRaw = leftEndpoint)
       (_witnessEqRight : witnessRaw = rightEndpoint),
       HEq someTerm
            (Term.refl (context := context) carrier witnessRaw) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.refl witnessRaw)),
        someType = Ty.id carrier leftEndpoint rightEndpoint →
        Σ' (witnessEqLeft : witnessRaw = leftEndpoint)
           (witnessEqRight : witnessRaw = rightEndpoint),
           HEq genericTerm
                (Term.refl (context := context) carrier witnessRaw) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsId
  cases genericTerm
  rename_i innerCarrier
  have idEq := Ty.id.inj someTypeIsId
  cases idEq.1
  exact ⟨idEq.2.1, idEq.2.2, HEq.rfl⟩

end LeanFX2
