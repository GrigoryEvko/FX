import LeanFX2.Reduction.ParRed.ParInductive.Inductive
import LeanFX2.Reduction.RawParInversion.AtomicCtors
import LeanFX2.Reduction.RawParInversion.CubicalAndIdentity
import LeanFX2.Reduction.RawParInversion.ModalAndAdvanced
import LeanFX2.Term.Inversion

/-! # LeanFX2.Term.PreservesTerm.TierTwoBinary

Tier 2 binary cong lifts for `RawStep.par`-to-`Step.par`
term-construction subject reduction.

Covers 10 ctors with two Term children at the same scope:
intervalMeet, intervalJoin, glueIntro, hcomp, codataUnfold,
sessionSend, listCons, equivApp, sessionRecv (Tier 1 single-child
no-β), refineIntro.

## Root status

Zero-axiom; carved from `Term/PreservesTerm.lean`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}


/-! ## Tier 2 — binary cong rules (no β/ι firing from the head)

Two Term children at the same scope, both contributing independent
parallel reductions.  Same recipe as Tier 1 unary, but with two IHs.

Recipe per binary ctor:
  obtain ⟨_, _, eq, leftStep, rightStep⟩ := <ctor>_inv rawStep
  obtain ⟨leftT,  leftSt⟩  := leftLift  leftStep
  obtain ⟨rightT, rightSt⟩ := rightLift rightStep
  cases eq
  exact ⟨Term.<ctor> ... leftT rightT,
         Step.par.<ctor>Cong leftSt rightSt⟩

Shipped this batch:
  * intervalMeet — both at Ty.interval
  * intervalJoin — both at Ty.interval
  * glueIntro    — both at baseType
  * hcomp        — both at carrierType
  * codataUnfold — different types (state, transition)
  * sessionSend  — different types (channel = session, payload)
  * effectPerform — different types (operation, arguments) -/

/-- **Tier 2 — Term.intervalMeet lift.** -/
theorem RawStep.par.lift_intervalMeet
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
    ∃ targetTerm : Term context Ty.interval targetRaw,
      Step.par (Term.intervalMeet leftValue rightValue) targetTerm := by
  obtain ⟨leftTargetRaw, rightTargetRaw, eq, leftStep, rightStep⟩ :=
    RawStep.par.intervalMeet_inv rawStep
  obtain ⟨leftTarget, leftStepTyped⟩ := leftLift leftStep
  obtain ⟨rightTarget, rightStepTyped⟩ := rightLift rightStep
  cases eq
  exact ⟨Term.intervalMeet leftTarget rightTarget,
         Step.par.intervalMeetCong leftStepTyped rightStepTyped⟩

/-- **Tier 2 — Term.intervalJoin lift.** -/
theorem RawStep.par.lift_intervalJoin
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
    ∃ targetTerm : Term context Ty.interval targetRaw,
      Step.par (Term.intervalJoin leftValue rightValue) targetTerm := by
  obtain ⟨leftTargetRaw, rightTargetRaw, eq, leftStep, rightStep⟩ :=
    RawStep.par.intervalJoin_inv rawStep
  obtain ⟨leftTarget, leftStepTyped⟩ := leftLift leftStep
  obtain ⟨rightTarget, rightStepTyped⟩ := rightLift rightStep
  cases eq
  exact ⟨Term.intervalJoin leftTarget rightTarget,
         Step.par.intervalJoinCong leftStepTyped rightStepTyped⟩

/-- **Tier 2 — Term.glueIntro lift.** -/
theorem RawStep.par.lift_glueIntro
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
    ∃ targetTerm : Term context (Ty.glue baseType boundaryWitness) targetRaw,
      Step.par
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness baseValue
                        partialValue)
        targetTerm := by
  obtain ⟨baseTargetRaw, partialTargetRaw, eq, baseStep, partialStep⟩ :=
    RawStep.par.glueIntro_inv rawStep
  obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
  obtain ⟨partialTarget, partialStepTyped⟩ := partialLift partialStep
  cases eq
  exact ⟨Term.glueIntro modeIsUnivalent baseType boundaryWitness baseTarget
                        partialTarget,
         Step.par.glueIntroCong modeIsUnivalent baseStepTyped partialStepTyped⟩

/-- **Tier 2 — Term.hcomp lift, cong arm only.**

D2.5.2 added raw-only `hcompBeta` / `hcompBetaDeep` β arms to
`RawStep.par`; their typed mirrors land in Phase B (separate
follow-up session).  Until then, this lift is restricted to the
cong arm — callers supply `sidesStep` and `capStep` directly
rather than inverting an opaque `RawStep.par (hcomp _ _) _`.

Mirrors `lift_transp_cong` (`EliminatorShallowBeta.lean`), which
takes the analogous narrow form for `transp` (whose β arms have
the same "raw-only ctor, no typed mirror" status). -/
theorem RawStep.par.lift_hcomp_cong
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
    {sidesTargetRaw capTargetRaw : RawTerm scope}
    (sidesStep : RawStep.par sidesRaw sidesTargetRaw)
    (capStep : RawStep.par capRaw capTargetRaw) :
    ∃ targetTerm :
        Term context carrierType (RawTerm.hcomp sidesTargetRaw capTargetRaw),
      Step.par (Term.hcomp modeIsUnivalent sidesValue capValue) targetTerm := by
  obtain ⟨sidesTarget, sidesStepTyped⟩ := sidesLift sidesStep
  obtain ⟨capTarget, capStepTyped⟩ := capLift capStep
  exact ⟨Term.hcomp modeIsUnivalent sidesTarget capTarget,
         Step.par.hcompCong modeIsUnivalent sidesStepTyped capStepTyped⟩

/-- **Tier 2 — Term.codataUnfold lift.** -/
theorem RawStep.par.lift_codataUnfold
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
    ∃ targetTerm : Term context (Ty.codata stateType outputType) targetRaw,
      Step.par (Term.codataUnfold initialState transition) targetTerm := by
  obtain ⟨stateTargetRaw, transitionTargetRaw, eq, stateStep, transitionStep⟩ :=
    RawStep.par.codataUnfold_inv rawStep
  obtain ⟨stateTarget, stateStepTyped⟩ := stateLift stateStep
  obtain ⟨transitionTarget, transitionStepTyped⟩ := transitionLift transitionStep
  cases eq
  exact ⟨Term.codataUnfold stateTarget transitionTarget,
         Step.par.codataUnfoldCong stateStepTyped transitionStepTyped⟩

/-- **Tier 2 — Term.sessionSend lift.** -/
theorem RawStep.par.lift_sessionSend
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
    ∃ targetTerm : Term context (Ty.session protocolStep) targetRaw,
      Step.par (Term.sessionSend protocolStep channel payload) targetTerm := by
  obtain ⟨channelTargetRaw, payloadTargetRaw, eq, channelStep, payloadStep⟩ :=
    RawStep.par.sessionSend_inv rawStep
  obtain ⟨channelTarget, channelStepTyped⟩ := channelLift channelStep
  obtain ⟨payloadTarget, payloadStepTyped⟩ := payloadLift payloadStep
  cases eq
  exact ⟨Term.sessionSend protocolStep channelTarget payloadTarget,
         Step.par.sessionSendCong channelStepTyped payloadStepTyped⟩

/-- **Tier 2 — Term.listCons lift.**  Two children: head (elementType)
and tail (listType elementType). -/
theorem RawStep.par.lift_listCons
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
    ∃ targetTerm : Term context (Ty.listType elementType) targetRaw,
      Step.par (Term.listCons headTerm tailTerm) targetTerm := by
  obtain ⟨headTargetRaw, tailTargetRaw, eq, headStep, tailStep⟩ :=
    RawStep.par.listCons_inv rawStep
  obtain ⟨headTarget, headStepTyped⟩ := headLift headStep
  obtain ⟨tailTarget, tailStepTyped⟩ := tailLift tailStep
  cases eq
  exact ⟨Term.listCons headTarget tailTarget,
         Step.par.listCons headStepTyped tailStepTyped⟩

/-- **Tier 2 — Term.equivApp lift.**  Two children: equiv (Ty.equiv A B)
and argument (A); result type B. -/
theorem RawStep.par.lift_equivApp
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
    ∃ targetTerm : Term context carrierB targetRaw,
      Step.par (Term.equivApp equivTerm argumentTerm) targetTerm := by
  obtain ⟨equivTargetRaw, argumentTargetRaw, eq, equivStep, argumentStep⟩ :=
    RawStep.par.equivApp_inv rawStep
  obtain ⟨equivTarget, equivStepTyped⟩ := equivLift equivStep
  obtain ⟨argumentTarget, argumentStepTyped⟩ := argumentLift argumentStep
  cases eq
  exact ⟨Term.equivApp equivTarget argumentTarget,
         Step.par.equivAppCong equivStepTyped argumentStepTyped⟩

/-- **Tier 1 — Term.sessionRecv lift.**  Single Term child (channel),
no β fires. -/
theorem RawStep.par.lift_sessionRecv
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (channelLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par channelRaw targetRawIH →
      ∃ channelTarget : Term context (Ty.session protocolStep) targetRawIH,
        Step.par channel channelTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.sessionRecv channelRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.session protocolStep) targetRaw,
      Step.par (Term.sessionRecv channel) targetTerm := by
  obtain ⟨channelTargetRaw, eq, channelStep⟩ := RawStep.par.sessionRecv_inv rawStep
  obtain ⟨channelTarget, channelStepTyped⟩ := channelLift channelStep
  cases eq
  exact ⟨Term.sessionRecv channelTarget,
         Step.par.sessionRecvCong channelStepTyped⟩

/-- **Tier 2 — Term.refineIntro lift.**  Two children: value (baseType)
and predicateProof (Ty.unit). -/
theorem RawStep.par.lift_refineIntro
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
    ∃ targetTerm : Term context (Ty.refine baseType predicate) targetRaw,
      Step.par (Term.refineIntro predicate baseValue predicateProof) targetTerm := by
  obtain ⟨valueTargetRaw, proofTargetRaw, eq, valueStep, proofStep⟩ :=
    RawStep.par.refineIntro_inv rawStep
  obtain ⟨valueTarget, valueStepTyped⟩ := valueLift valueStep
  obtain ⟨proofTarget, proofStepTyped⟩ := proofLift proofStep
  cases eq
  exact ⟨Term.refineIntro predicate valueTarget proofTarget,
         Step.par.refineIntroCong valueStepTyped proofStepTyped⟩

end LeanFX2
