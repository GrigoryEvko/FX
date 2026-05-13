import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Term.Inversion

/-! # LeanFX2.Term.PreservesTerm.SchematicValueCtors

Full lifts for schematic-payload value ctors and funext-family
ctors whose Term-level content is a raw witness rather than a typed
Term child.  Each uses a newly-added typed Step.par cong rule that
consumes the raw witness reduction directly.

Covers shipped (8): oeqRefl, idStrictRefl, refl, equivReflId,
equivReflIdAtId, uaIntroHet, equivIntroHet, oeqFunext;
plus three deferred funext-family stubs (funextRefl,
funextReflAtId, funextIntroHet).

## Root status

Zero-axiom; carved from `Term/PreservesTerm.lean`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}


/-! ## Schematic-payload value ctors with typed cong rules

`Term.oeqRefl` and `Term.idStrictRefl` are schematic-payload value
ctors — their only Term-level computational content is a raw witness.
Both have typed Step.par cong rules (`oeqReflCong`, `idStrictReflCong`)
that take a `RawStep.par` on the witness raw and produce a typed
Step.par at heterogeneous source/target types (the carrier's left and
right endpoints both reduce in lockstep with the witness).

These lifts don't take a typed-IH parameter — the cong rule consumes
the raw step directly.  This makes them genuinely Tier 0.5 (atom-like
but with raw cong). -/

/-- **Term.oeqRefl full lift.**  No typed IH needed — `oeqReflCong`
takes the raw step directly. -/
theorem RawStep.par.lift_full_oeqRefl
    (carrier : Ty level scope) (rawWitness : RawTerm scope)
    (sourceTerm :
      Term context (Ty.oeq carrier rawWitness rawWitness)
                   (RawTerm.oeqRefl rawWitness))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.oeqRefl rawWitness) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨witnessTarget, eq, witnessStep⟩ := RawStep.par.oeqRefl_inv rawStep
  cases eq
  -- Use Term.oeqRefl_unique to align sourceTerm with the canonical Term.oeqRefl:
  -- Actually sourceTerm has type Ty.oeq carrier rawWitness rawWitness with raw
  -- RawTerm.oeqRefl rawWitness, which forces it to be Term.oeqRefl carrier rawWitness.
  -- But cases on sourceTerm would hit dep-elim wall; use a destructor.
  refine ⟨Ty.oeq carrier witnessTarget witnessTarget,
          Term.oeqRefl (context := context) carrier witnessTarget, ?_⟩
  -- Need: Step.par sourceTerm (Term.oeqRefl carrier witnessTarget)
  -- Use suffices to force sourceTerm to be Term.oeqRefl _ rawWitness:
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.oeqRefl rawWitness)),
        someType = Ty.oeq carrier rawWitness rawWitness →
        Step.par genericTerm
                 (Term.oeqRefl (context := context) carrier witnessTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsOeq
  cases genericTerm
  rename_i innerCarrier
  have oeqEq := Ty.oeq.inj someTypeIsOeq
  cases oeqEq.1
  exact Step.par.oeqReflCong witnessStep

/-- **Term.idStrictRefl full lift.** -/
theorem RawStep.par.lift_full_idStrictRefl
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level scope) (rawWitness : RawTerm scope)
    (sourceTerm :
      Term context (Ty.idStrict carrier rawWitness rawWitness)
                   (RawTerm.idStrictRefl rawWitness))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.idStrictRefl rawWitness) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨witnessTarget, eq, witnessStep⟩ := RawStep.par.idStrictRefl_inv rawStep
  cases eq
  refine ⟨Ty.idStrict carrier witnessTarget witnessTarget,
          Term.idStrictRefl (context := context) modeIsStrict carrier
                            witnessTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.idStrictRefl rawWitness)),
        someType = Ty.idStrict carrier rawWitness rawWitness →
        Step.par genericTerm
                 (Term.idStrictRefl (context := context) modeIsStrict carrier
                                    witnessTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsIdStrict
  cases genericTerm
  rename_i innerMode innerCarrier
  have idStrictEq := Ty.idStrict.inj someTypeIsIdStrict
  cases idStrictEq.1
  exact Step.par.idStrictReflCong modeIsStrict witnessStep

/-! ## Schematic-payload value ctors with new typed cong rules

`Term.refl carrier rawWitness`'s only computational content is the
schematic raw `rawWitness`.  `Step.par.reflCong` was added in the prior
juggernaut to lift `RawStep.par.reflCong` to the typed level: a raw step
on the witness produces a typed step on the wrapper.

`Term.funextRefl`, `Term.funextReflAtId`, `Term.funextIntroHet` follow
the same pattern with their respective new cong rules. -/

/-- **Term.refl full lift.**  No typed IH needed — `reflCong` consumes the
raw step directly.  Source type `Ty.id carrier rawWitness rawWitness`;
target type after step is `Ty.id carrier witnessTarget witnessTarget`. -/
theorem RawStep.par.lift_full_refl
    (carrier : Ty level scope) (rawWitness : RawTerm scope)
    (sourceTerm :
      Term context (Ty.id carrier rawWitness rawWitness)
                   (RawTerm.refl rawWitness))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.refl rawWitness) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨witnessTarget, eq, witnessStep⟩ := RawStep.par.refl_inv rawStep
  cases eq
  refine ⟨Ty.id carrier witnessTarget witnessTarget,
          Term.refl (context := context) carrier witnessTarget, ?_⟩
  -- Force sourceTerm to be Term.refl _ rawWitness via free-the-type:
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.refl rawWitness)),
        someType = Ty.id carrier rawWitness rawWitness →
        Step.par genericTerm
                 (Term.refl (context := context) carrier witnessTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsId
  cases genericTerm
  rename_i innerCarrier
  have idEq := Ty.id.inj someTypeIsId
  cases idEq.1
  exact Step.par.reflCong carrier witnessStep

/-! ## Funext-family schematic-payload lifts

`Term.funextRefl`, `Term.funextReflAtId`, `Term.funextIntroHet` all
have raw form `RawTerm.lam (RawTerm.refl applyRaw)` (with applyRaw at
scope+1).  Their typed cong rules (added in the prior juggernaut)
take a raw step on applyRaw and produce a typed Step.par on the
wrapper.  Each lift uses lam_inv + refl_inv to extract the inner
applyRaw step from the raw target. -/

/-! ### Term.funextRefl full lift — DEFERRED

Term.funextRefl's raw form `RawTerm.lam (RawTerm.refl applyRaw)` is
SHARED with Term.lamPi (Term.refl ...) at the same Ty.piTy domainType
(Ty.id codomainType.weaken applyRaw applyRaw) type.  Both ctors
inhabit identical (typed × raw) signatures.  Generic lift dispatch
via `cases genericTerm` produces both arms; the lamPi case requires
constructing Step.par from Term.lamPi to Term.funextRefl, which is
NOT a Step.par cong rule (would require a "Term.lamPi-to-funextRefl"
ctor that ETA-equates the two structurally-distinct ctors).

A clean lift requires either:
1. A new Step.par ctor witnessing the two ctors are convertible (an
   eta-style rule for funextRefl).
2. A Term.unique lemma saying lamPi (refl ...) and funextRefl
   constructed at the same (Ty, raw) signature are HEq.
3. Restricting the headline existential to allow Term.lamPi witnesses
   (since they have identical raw shape, the down-stream confluence
   chain cares about raw, not syntactic Term).

Deferred to a separate commit alongside the headline assembly. -/

/-! ### Term.funextReflAtId full lift — DEFERRED

Term.funextReflAtId's raw form `RawTerm.lam (RawTerm.refl applyRaw)`
collides at the (Ty.id (Ty.arrow ...) ...) type with multiple Term
ctors (Term.lam, Term.lamPi, Term.funextRefl, Term.funextIntroHet).
The `cases genericTerm` + `all_goals first | nomatch | ...` pattern
that ALMOST works at the surface level was found to LEAK 2 axioms
(Quot.sound, propext) per the per-decl audit gate — the indexed-
inductive partial-match trap (memorized) fires on the multi-ctor
dispatch.

The fix requires using ctor-by-ctor explicit `casesOn` with motive,
or matching on raw projection via `Term.toRaw`-shape dispatch.  Both
are deferred to the headline assembly phase where the dispatch can
branch cleanly on Term ctor IDs. -/

/-! ### Term.funextIntroHet full lift — DEFERRED

Term.funextIntroHet's raw form `RawTerm.lam (RawTerm.refl applyARaw)`
is shape-collision with Term.funextReflAtId at Ty.id types — when the
applyARaw happens to be `RawTerm.refl applyRaw'`, both ctors have
identical (Ty, raw) signatures.  Generic dispatch surfaces both arms;
constructing a Step.par from Term.funextReflAtId to Term.funextIntroHet
is not a single Step.par ctor — it would require composing through
the eqArrow / eqArrowHet rules, which target funextRefl / funextRefl
respectively, not funextIntroHet directly.

Deferred to the headline assembly phase, where the dispatch can branch
on the actual source ctor and use ctor-specific Step.par rules. -/

/-! ## Atom-shaped value ctors (equivReflId, equivReflIdAtId)

`Term.equivReflId carrier` and `Term.equivReflIdAtId innerLevel innerLevelLt
carrier carrierRaw` are atom-shaped values with raw form
`RawTerm.equivIntro (lam (var 0)) (lam (var 0))`.  The id-lam bodies are
fixed `RawTerm.var 0`, which only refl-step.  Therefore the only raw
step from this composed shape is `refl`, and the typed lift returns the
source term itself with `Step.par.refl`. -/

/-- **Term.equivReflId full lift.**  Atom-shaped — only refl applies. -/
theorem RawStep.par.lift_full_equivReflId
    (carrier : Ty level scope)
    (sourceTerm :
      Term context (Ty.equiv carrier carrier)
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  -- The id-lam body is var 0; var only refl-steps; lam_inv yields target = lam (var 0).
  obtain ⟨forwardTarget, backwardTarget, eqOuter, forwardStep, backwardStep⟩ :=
    RawStep.par.equivIntro_inv rawStep
  obtain ⟨forwardBody, fEqLam, fBodyStep⟩ := RawStep.par.lam_inv forwardStep
  have fBodyVar := RawStep.par.var_inv fBodyStep
  cases fBodyVar
  cases fEqLam
  obtain ⟨backwardBody, bEqLam, bBodyStep⟩ := RawStep.par.lam_inv backwardStep
  have bBodyVar := RawStep.par.var_inv bBodyStep
  cases bBodyVar
  cases bEqLam
  cases eqOuter
  exact ⟨Ty.equiv carrier carrier, sourceTerm, Step.par.refl sourceTerm⟩

/-- **Term.equivReflIdAtId full lift.**  Atom-shaped — only refl applies. -/
theorem RawStep.par.lift_full_equivReflIdAtId
    (innerLevel : UniverseLevel) (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope) (carrierRaw : RawTerm scope)
    (sourceTerm :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) carrierRaw carrierRaw)
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨forwardTarget, backwardTarget, eqOuter, forwardStep, backwardStep⟩ :=
    RawStep.par.equivIntro_inv rawStep
  obtain ⟨forwardBody, fEqLam, fBodyStep⟩ := RawStep.par.lam_inv forwardStep
  have fBodyVar := RawStep.par.var_inv fBodyStep
  cases fBodyVar
  cases fEqLam
  obtain ⟨backwardBody, bEqLam, bBodyStep⟩ := RawStep.par.lam_inv backwardStep
  have bBodyVar := RawStep.par.var_inv bBodyStep
  cases bBodyVar
  cases bEqLam
  cases eqOuter
  exact ⟨Ty.id (Ty.universe innerLevel innerLevelLt) carrierRaw carrierRaw,
         sourceTerm, Step.par.refl sourceTerm⟩

/-! ## Heterogeneous-carrier ctors with single typed equivWitness child

`Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness`
has a single typed `equivWitness : Term context (Ty.equiv carrierA carrierB)
(RawTerm.equivIntro forwardRaw backwardRaw)` child.  The raw form is the
SAME `RawTerm.equivIntro forwardRaw backwardRaw` as the equivWitness.

The lift takes an equivWitness lift IH; from `RawStep.par.equivIntro_inv`
we get a target raw that matches RawTerm.equivIntro forward' backward'.
Apply Step.par.uaIntroHetCong with the typed step. -/

/-- **Term.uaIntroHet full lift.** Single typed child (equivWitness) at
`Ty.equiv carrierA carrierB`. -/
theorem RawStep.par.lift_full_uaIntroHet
    (innerLevel : UniverseLevel) (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness : Term context (Ty.equiv carrierA carrierB)
                                 (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivWitnessLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par (RawTerm.equivIntro forwardRaw backwardRaw) targetRawIH →
      ∃ equivWitnessTarget :
          Term context (Ty.equiv carrierA carrierB) targetRawIH,
        Step.par equivWitness equivWitnessTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.equivIntro forwardRaw backwardRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.uaIntroHet (context := context) innerLevel innerLevelLt
                         carrierARaw carrierBRaw equivWitness)
        targetTerm := by
  -- Use equivIntro_inv to extract target shape
  obtain ⟨forwardTarget, backwardTarget, eqOuter, _, _⟩ :=
    RawStep.par.equivIntro_inv rawStep
  -- Apply equivWitness lift IH (passing the full rawStep) to get typed target
  obtain ⟨equivWitnessTarget, equivWitnessStepTyped⟩ := equivWitnessLift rawStep
  cases eqOuter
  refine ⟨Ty.id (Ty.universe innerLevel innerLevelLt) carrierARaw carrierBRaw, ?_, ?_⟩
  · -- equivWitnessTarget at Ty.equiv carrierA carrierB with raw equivIntro forwardTarget backwardTarget;
    -- we want a typed Term at Ty.id (Ty.universe ...) carrierARaw carrierBRaw with the same raw.
    -- Use Term.uaIntroHet to wrap.
    exact Term.uaIntroHet (context := context) innerLevel innerLevelLt
                          carrierARaw carrierBRaw equivWitnessTarget
  · exact Step.par.uaIntroHetCong innerLevel innerLevelLt
                                  carrierARaw carrierBRaw equivWitnessStepTyped

/-! ## Heterogeneous-carrier equivalence intro lift

`Term.equivIntroHet forward backward leftInv rightInv` has four typed
children but only `forward` + `backward` appear in the raw projection
`RawTerm.equivIntro forwardRaw backwardRaw`.  The cong rule
`Step.par.equivIntroHetCong` takes Step.par on forward + backward and
auto-constructs the leftInv/rightInv with new types.

The lift takes IHs on forward and backward only.  The leftInv/rightInv
inputs are passed through as schematic implicits to the cong rule. -/

/-- **Term.equivIntroHet full lift.** -/
theorem RawStep.par.lift_full_equivIntroHet
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    (forward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
    (backward : Term context (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv :
      Term context
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInv :
      Term context
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw)
    (forwardLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par forwardRaw targetRawIH →
      ∃ forwardTarget : Term context (Ty.arrow carrierA carrierB) targetRawIH,
        Step.par forward forwardTarget)
    (backwardLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par backwardRaw targetRawIH →
      ∃ backwardTarget : Term context (Ty.arrow carrierB carrierA) targetRawIH,
        Step.par backward backwardTarget)
    (leftInvNewSource :
      ∀ (forwardTarget backwardTarget : RawTerm scope),
      Term context
        (equivIntroHetLeftInverseType carrierA forwardTarget backwardTarget)
        leftInvRaw)
    (rightInvNewSource :
      ∀ (forwardTarget backwardTarget : RawTerm scope),
      Term context
        (equivIntroHetRightInverseType carrierB forwardTarget backwardTarget)
        rightInvRaw)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.equivIntro forwardRaw backwardRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.equivIntroHet (context := context) forward backward leftInv rightInv)
        targetTerm := by
  obtain ⟨forwardTarget, backwardTarget, eqOuter, forwardStep, backwardStep⟩ :=
    RawStep.par.equivIntro_inv rawStep
  obtain ⟨forwardTyped, forwardStepTyped⟩ := forwardLift forwardStep
  obtain ⟨backwardTyped, backwardStepTyped⟩ := backwardLift backwardStep
  cases eqOuter
  refine ⟨Ty.equiv carrierA carrierB,
          Term.equivIntroHet (context := context) forwardTyped backwardTyped
                             (leftInvNewSource forwardTarget backwardTarget)
                             (rightInvNewSource forwardTarget backwardTarget),
          ?_⟩
  exact Step.par.equivIntroHetCong forwardStepTyped backwardStepTyped

theorem RawStep.par.lift_full_oeqFunext
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    (pointwiseProof :
      Term context
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw)
    (pointwiseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pointwiseRaw targetRawIH →
      ∃ pointwiseTarget :
          Term context
            (oeqFunextPointwiseType domainType codomainType
              leftFunctionRaw rightFunctionRaw)
            targetRawIH,
        Step.par pointwiseProof pointwiseTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.oeqFunext pointwiseRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseProof)
        targetTerm := by
  obtain ⟨pointwiseTargetRaw, eq, pointwiseStep⟩ :=
    RawStep.par.oeqFunext_inv rawStep
  obtain ⟨pointwiseTarget, pointwiseStepTyped⟩ := pointwiseLift pointwiseStep
  cases eq
  refine
    ⟨Ty.oeq (Ty.arrow domainType codomainType) leftFunctionRaw rightFunctionRaw,
     Term.oeqFunext domainType codomainType leftFunctionRaw rightFunctionRaw
                    pointwiseTarget, ?_⟩
  exact Step.par.oeqFunextCong domainType codomainType
                               leftFunctionRaw rightFunctionRaw
                               pointwiseStepTyped

end LeanFX2
