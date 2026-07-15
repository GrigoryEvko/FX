import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.ModeOmega

/-! # FX1PolyAudit/AuditAxisModeModeOmega — zero-axiom gate for mode-21 (CAPSTONE)

Per-declaration zero-axiom gate for `mode-21` (`FX1Poly/Axis/Mode/ModeOmega.lean`): the decidable 2-cell
equality machine, the `ModeOmega` bundle + its decidable admissibility certificate, the FX / cohesion / clock
witnesses, the headline theorems (admissibility by `decide`, the structure-class tie, multimodality, the O-COMBINE
amalgamation, 2-cell reflexivity), and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The decidable 2-cell equality machine (mode-3 lifted)
#assert_no_axioms FX1Poly.Axis.DecidableTwoCellEquality
#assert_no_axioms FX1Poly.Axis.DecidableTwoCellEquality.equal
#assert_no_axioms FX1Poly.Axis.DecidableTwoCellEquality.equal_refl
#assert_no_axioms FX1Poly.Axis.DecidableTwoCellEquality.equal_complete
#assert_no_axioms FX1Poly.Axis.DecidableTwoCellEquality.equal_sound
#assert_no_axioms FX1Poly.Axis.DecidableTwoCellEquality.equal_iff
#assert_no_axioms FX1Poly.Axis.StrictTwoCellNormalForm
#assert_no_axioms FX1Poly.Axis.strictTwoCellEquality

-- The bundle + its decidable admissibility certificate
#assert_no_axioms FX1Poly.Axis.ModeOmega
#assert_no_axioms FX1Poly.Axis.ModeOmega.isAdmissible

-- The witnesses (FX / cohesion / clock)
#assert_no_axioms FX1Poly.Axis.fxModeDoctrine
#assert_no_axioms FX1Poly.Axis.fxModeOmega
#assert_no_axioms FX1Poly.Axis.cohesionModeOmega
#assert_no_axioms FX1Poly.Axis.ClockMode
#assert_no_axioms FX1Poly.Axis.ClockModality
#assert_no_axioms FX1Poly.Axis.clockModeGraph
#assert_no_axioms FX1Poly.Axis.clockModeSignature
#assert_no_axioms FX1Poly.Axis.clockModeOmega

-- The headline theorems
#assert_no_axioms FX1Poly.Axis.fxModeOmega_isAdmissible
#assert_no_axioms FX1Poly.Axis.cohesionModeOmega_isAdmissible
#assert_no_axioms FX1Poly.Axis.clockModeOmega_isAdmissible
#assert_no_axioms FX1Poly.Axis.fxModeOmega_modalities_supportDiagonal
#assert_no_axioms FX1Poly.Axis.fxModeOmega_isMultimodal
#assert_no_axioms FX1Poly.Axis.modeOmega_combine_admissible
#assert_no_axioms FX1Poly.Axis.strictTwoCellEquality_refl
#assert_no_axioms FX1Poly.Axis.strictTwoCellEquality_discriminates
#assert_no_axioms FX1Poly.Axis.unsoundDoctrine
#assert_no_axioms FX1Poly.Axis.unsoundModeOmega
#assert_no_axioms FX1Poly.Axis.unsoundModeOmega_isInadmissible
#assert_no_axioms FX1Poly.Axis.fxModeOmega_signature_isFxAxis

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasModeOmegaWeakGray
#assert_no_axioms FX1Poly.Axis.fxMode_hasModeOmegaGeneralMultiplier
#assert_no_axioms FX1Poly.Axis.fxMode_hasModeOmegaCanonicityTransport
#assert_no_axioms FX1Poly.Axis.fxMode_hasModeOmegaKernelFibration

end FX1PolyAudit
