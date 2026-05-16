import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Term.Inversion

/-! # LeanFX2.Term.PreservesTerm.EliminatorIdentityFamily

Cong-only lift theorems for the three identity-family eliminators:

* `lift_idJ_cong` — HoTT identity-type eliminator `J` (`Term.idJ`).
* `lift_oeqJ_cong` — observational-equality eliminator (`Term.oeqJ`).
* `lift_idStrictRec_cong` — strict-identity recursor
  (`Term.idStrictRec`, mode-strict gated).

Each takes raw parallel-reduction steps on the base case and witness
subterms together with per-subterm typed-lift callbacks, and assembles
the typed `Step.par.<idJ|oeqJCong|idStrictRecCong>` cong witness directly.
This is the cong-only variant for CONVTRANS-B.2c (ticket #1724); the
ι-canonical arms (iotaIdJReflDeep / iotaIdStrictRecReflDeep, and the
absence of an oeqJ ι-rule) live in matching full lifts to be shipped
later in the CONVTRANS-B.2 cascade.

## Structural notes

All three identity-family eliminators share the same shape:

* Constant motive `motiveType : Ty level scope` (output type
  independent of witness target raw).
* Two raw subterms: `baseRaw` (refl-case payload) and `witnessRaw`
  (path / equality proof).
* Output raw shape `RawTerm.<X> baseTargetRaw witnessTargetRaw`.

The typed cong rules differ only in:

* `Step.par.idJ` — no mode constraint, witness at `Ty.id carrier ...`.
* `Step.par.oeqJCong` — no mode constraint, witness at
  `Ty.oeq carrier ...`.
* `Step.par.idStrictRecCong` — takes `modeIsStrict : mode = Mode.strict`
  explicit, witness at `Ty.idStrict carrier ...`.

## Root status

Zero-axiom; mirrors the pattern in `EliminatorConstantMotive.lean`
(commit ae4959a). -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- **CONVTRANS-B.2c — Term.idJ lift, cong arm only.**  HoTT identity
J eliminator: witness at `Ty.id carrier leftEndpoint rightEndpoint`,
output at constant `motiveType`.  ι-arm `iotaIdJReflDeep` (refl
witness) lives in a future full variant. -/
theorem RawStep.par.lift_idJ_cong
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context motiveType targetRawIH,
        Step.par baseCase baseTarget)
    (witnessLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par witnessRaw targetRawIH →
      ∃ witnessTarget :
          Term context (Ty.id carrier leftEndpoint rightEndpoint) targetRawIH,
        Step.par witness witnessTarget)
    {baseTargetRaw witnessTargetRaw : RawTerm scope}
    (baseStep : RawStep.par baseRaw baseTargetRaw)
    (witnessStep : RawStep.par witnessRaw witnessTargetRaw) :
    ∃ targetTerm :
        Term context motiveType
                     (RawTerm.idJ baseTargetRaw witnessTargetRaw),
      Step.par (Term.idJ baseCase witness) targetTerm := by
  obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
  obtain ⟨witnessTarget, witnessStepTyped⟩ := witnessLift witnessStep
  exact ⟨Term.idJ baseTarget witnessTarget,
         Step.par.idJ baseStepTyped witnessStepTyped⟩

/-- **CONVTRANS-B.2c — Term.oeqJ lift, cong arm only.**  Observational-
equality J eliminator: witness at `Ty.oeq carrier leftEndpoint
rightEndpoint`, output at constant `motiveType`.  oeqJ has no ι-rule in
the kernel (no oeq-canonical β yet), so this cong-only lift is the
total raw inversion projection for oeqJ. -/
theorem RawStep.par.lift_oeqJ_cong
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context motiveType targetRawIH,
        Step.par baseCase baseTarget)
    (witnessLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par witnessRaw targetRawIH →
      ∃ witnessTarget :
          Term context (Ty.oeq carrier leftEndpoint rightEndpoint) targetRawIH,
        Step.par witness witnessTarget)
    {baseTargetRaw witnessTargetRaw : RawTerm scope}
    (baseStep : RawStep.par baseRaw baseTargetRaw)
    (witnessStep : RawStep.par witnessRaw witnessTargetRaw) :
    ∃ targetTerm :
        Term context motiveType
                     (RawTerm.oeqJ baseTargetRaw witnessTargetRaw),
      Step.par (Term.oeqJ baseCase witness) targetTerm := by
  obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
  obtain ⟨witnessTarget, witnessStepTyped⟩ := witnessLift witnessStep
  exact ⟨Term.oeqJ baseTarget witnessTarget,
         Step.par.oeqJCong baseStepTyped witnessStepTyped⟩

/-- **CONVTRANS-B.2c — Term.idStrictRec lift, cong arm only.**  Strict-
identity recursor (mode-strict gated): witness at `Ty.idStrict carrier
leftEndpoint rightEndpoint`, output at constant `motiveType`.  ι-arm
`iotaIdStrictRecReflDeep` (refl witness) lives in a future full
variant.  The `modeIsStrict` proof rides through both source and
target terms as a `mode = Mode.strict` constraint. -/
theorem RawStep.par.lift_idStrictRec_cong
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context motiveType targetRawIH,
        Step.par baseCase baseTarget)
    (witnessLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par witnessRaw targetRawIH →
      ∃ witnessTarget :
          Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
                       targetRawIH,
        Step.par witness witnessTarget)
    {baseTargetRaw witnessTargetRaw : RawTerm scope}
    (baseStep : RawStep.par baseRaw baseTargetRaw)
    (witnessStep : RawStep.par witnessRaw witnessTargetRaw) :
    ∃ targetTerm :
        Term context motiveType
                     (RawTerm.idStrictRec baseTargetRaw witnessTargetRaw),
      Step.par (Term.idStrictRec modeIsStrict baseCase witness) targetTerm := by
  obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
  obtain ⟨witnessTarget, witnessStepTyped⟩ := witnessLift witnessStep
  exact ⟨Term.idStrictRec modeIsStrict baseTarget witnessTarget,
         Step.par.idStrictRecCong modeIsStrict baseStepTyped witnessStepTyped⟩

end LeanFX2
