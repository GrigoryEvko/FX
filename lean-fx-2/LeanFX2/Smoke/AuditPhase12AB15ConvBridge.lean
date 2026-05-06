import LeanFX2.Reduction.ConvBridge

/-! # Smoke/AuditPhase12AB15ConvBridge — Conv ↔ ConvCumul real bridge audit.

Audits the FULL real bridge between `Conv` and `ConvCumul`,
including:

* `Step.toConvCumul` — every Step ctor (52 total: 35 cong + 17 β/ι)
  lifts to a ConvCumul.  Real recursion, real body.
* `StepStar.toConvCumul` — chain induction (refl + trans).
* `Conv.toConvCumul` — real proof: decompose existential triple
  via `obtain`, lift two StepStar legs, sym one, trans together.
* `ConvCumul.refl_toConv` + roundtrip helpers — refl-restricted
  backward direction (homogeneous-ctx only).
* 17 `ConvCumul.X_toConv` lift theorems for β/ι ctors at the
  homogeneous fragment.
* Inverse theorems (Phase 6 / CUMUL-5.3) on the refl fragment.

## What did NOT ship (and why)

* Full `ConvCumul → Conv` is not generally available because:
  - `ConvCumul.viaUp` relates Terms at distinct contexts/levels.
  - `ConvCumul.cumulUpCong` similarly cross-context.
  - `ConvCumul.trans` projection requires Conv.trans which needs
    Church-Rosser (Layer 3, deferred).

These restrictions are NOT "blockers" but REAL architectural
limits given the kernel state.  The forward direction is COMPLETE.

## Audit

Every `#print axioms` below MUST report
"does not depend on any axioms". -/

namespace LeanFX2

#print axioms Step.toConvCumul
#print axioms StepStar.toConvCumul
#print axioms Conv.toConvCumul

#print axioms Conv.refl_toConvCumul
#print axioms ConvCumul.refl_toConv
#print axioms Conv.toConvCumul_toConv_refl
#print axioms ConvCumul.toConv_toConvCumul_refl
#print axioms Conv.sym_via_ConvCumul_refl
#print axioms ConvCumul.sym_via_refl

#print axioms Step.toConv_toConvCumul

#print axioms ConvCumul.betaAppCumul_toConv
#print axioms ConvCumul.betaAppPiCumul_toConv
#print axioms ConvCumul.betaFstPairCumul_toConv
#print axioms ConvCumul.betaSndPairCumul_toConv
#print axioms ConvCumul.iotaBoolElimTrueCumul_toConv
#print axioms ConvCumul.iotaBoolElimFalseCumul_toConv
#print axioms ConvCumul.iotaNatElimZeroCumul_toConv
#print axioms ConvCumul.iotaNatElimSuccCumul_toConv
#print axioms ConvCumul.iotaNatRecZeroCumul_toConv
#print axioms ConvCumul.iotaNatRecSuccCumul_toConv
#print axioms ConvCumul.iotaListElimNilCumul_toConv
#print axioms ConvCumul.iotaListElimConsCumul_toConv
#print axioms ConvCumul.iotaOptionMatchNoneCumul_toConv
#print axioms ConvCumul.iotaOptionMatchSomeCumul_toConv
#print axioms ConvCumul.iotaEitherMatchInlCumul_toConv
#print axioms ConvCumul.iotaEitherMatchInrCumul_toConv
#print axioms ConvCumul.iotaIdJReflCumul_toConv

#print axioms Step.toConvCumul_back_to_Conv
#print axioms StepStar.toConvCumul_back_to_Conv
#print axioms Conv.fromStep_eq_fromStepStar_fromStep

#print axioms Conv.refl_inverse_roundtrip_A
#print axioms ConvCumul.refl_inverse_roundtrip_B
#print axioms ConvCumul.betaApp_roundtrip_eq
#print axioms ConvCumul.refl_inverse_identity
#print axioms Conv.refl_inverse_identity

/-! ## Real-fragment β/ι roundtrip example

A β-redex roundtrip: lift a `Step.betaApp` to `ConvCumul`, project
back to `Conv` via the matching β/ι Conv-helper.  Body should
type-check, demonstrating Phase 7 audit. -/

/-- β-redex roundtrip example: works at any context. -/
example
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
    (bodyTerm :
      Term (context.cons domainType) codomainType.weaken bodyRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    ConvCumul (Term.app (Term.lam (codomainType := codomainType) bodyTerm) argumentTerm)
              (Term.subst0 bodyTerm argumentTerm) :=
  Step.toConvCumul (Step.betaApp bodyTerm argumentTerm)

/-- ι-redex roundtrip example. -/
example
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {thenRaw elseRaw : RawTerm scope}
    (thenBranch : Term context
      (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch : Term context
      (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    ConvCumul (Term.boolElim Term.boolTrue thenBranch elseBranch) thenBranch :=
  Step.toConvCumul (Step.iotaBoolElimTrue thenBranch elseBranch)

/-- cong roundtrip example: appLeft inner step lifts to appCong. -/
example
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRawA functionRawB argumentRaw : RawTerm scope}
    {functionTermA functionTermB :
      Term context (Ty.arrow domainType codomainType) functionRawA}
    {argumentTerm : Term context domainType argumentRaw}
    (innerStep : Step functionTermA functionTermB) :
    ConvCumul (Term.app functionTermA argumentTerm)
              (Term.app functionTermB argumentTerm) :=
  Step.toConvCumul (Step.appLeft innerStep)

/-- ConvCumul-promote-then-Conv-project at matched level via the
βι helpers (real composition). -/
example
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
    (bodyTerm :
      Term (context.cons domainType) codomainType.weaken bodyRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Conv (Term.app (Term.lam (codomainType := codomainType) bodyTerm) argumentTerm)
         (Term.subst0 bodyTerm argumentTerm) :=
  ConvCumul.betaAppCumul_toConv bodyTerm argumentTerm

end LeanFX2
