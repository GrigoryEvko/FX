import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.ModeOmega

/-! # FX1PolyAudit/AuditTier0ModeModeOmega — zero-axiom gate for mode-21 (CAPSTONE)

Per-declaration zero-axiom gate for `mode-21` (`FX1Poly/Tier0/Mode/ModeOmega.lean`): the decidable 2-cell
equality machine, the `ModeOmega` bundle + its decidable admissibility certificate, the FX / cohesion / clock
witnesses, the headline theorems (admissibility by `decide`, the structure-class tie, multimodality, the O-COMBINE
amalgamation, 2-cell reflexivity), and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The decidable 2-cell equality machine (mode-3 lifted)
#assert_no_axioms FX1Poly.Tier0.DecidableTwoCellEquality
#assert_no_axioms FX1Poly.Tier0.DecidableTwoCellEquality.equal
#assert_no_axioms FX1Poly.Tier0.DecidableTwoCellEquality.equal_refl
#assert_no_axioms FX1Poly.Tier0.StrictTwoCellNormalForm
#assert_no_axioms FX1Poly.Tier0.strictTwoCellEquality

-- The bundle + its decidable admissibility certificate
#assert_no_axioms FX1Poly.Tier0.ModeOmega
#assert_no_axioms FX1Poly.Tier0.ModeOmega.isAdmissible

-- The witnesses (FX / cohesion / clock)
#assert_no_axioms FX1Poly.Tier0.fxModeDoctrine
#assert_no_axioms FX1Poly.Tier0.fxModeOmega
#assert_no_axioms FX1Poly.Tier0.cohesionModeOmega
#assert_no_axioms FX1Poly.Tier0.ClockMode
#assert_no_axioms FX1Poly.Tier0.ClockModality
#assert_no_axioms FX1Poly.Tier0.clockModeGraph
#assert_no_axioms FX1Poly.Tier0.clockModeSignature
#assert_no_axioms FX1Poly.Tier0.clockModeOmega

-- The headline theorems
#assert_no_axioms FX1Poly.Tier0.fxModeOmega_isAdmissible
#assert_no_axioms FX1Poly.Tier0.cohesionModeOmega_isAdmissible
#assert_no_axioms FX1Poly.Tier0.clockModeOmega_isAdmissible
#assert_no_axioms FX1Poly.Tier0.fxModeOmega_modalities_supportDiagonal
#assert_no_axioms FX1Poly.Tier0.fxModeOmega_isMultimodal
#assert_no_axioms FX1Poly.Tier0.modeOmega_combine_admissible
#assert_no_axioms FX1Poly.Tier0.strictTwoCellEquality_refl

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModeOmegaWeakGray
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModeOmegaGeneralMultiplier
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModeOmegaCanonicityTransport
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModeOmegaKernelFibration

end FX1PolyAudit
