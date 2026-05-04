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

end LeanFX2
