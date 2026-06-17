import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Presentation

/-! # FX1PolyAudit/AuditTier0ModePresentation — zero-axiom gate for mode-27

Per-declaration zero-axiom gate for `mode-27` (`FX1Poly/Tier0/Mode/Presentation.lean`): the three modal-context
presentations (MTT / Fitch / dual-context) + their depth measures, the Fitch ↔ dual-context bijection, the
Fitch → MTT flattening + lock-depth preservation, the tri-presentation depth agreement, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The three context representations + depth measures
#assert_no_axioms FX1Poly.Tier0.MttEntry
#assert_no_axioms FX1Poly.Tier0.MttContext.lockCount
#assert_no_axioms FX1Poly.Tier0.FitchContext.lockDepth
#assert_no_axioms FX1Poly.Tier0.DualContext

-- The Fitch <-> dual-context bijection (Pfenning-Davies = single-lock Fitch)
#assert_no_axioms FX1Poly.Tier0.dualToFitch
#assert_no_axioms FX1Poly.Tier0.fitchToDual
#assert_no_axioms FX1Poly.Tier0.fitchToDual_dualToFitch
#assert_no_axioms FX1Poly.Tier0.dualToFitch_fitchToDual
#assert_no_axioms FX1Poly.Tier0.dualToFitch_lockDepth

-- The Fitch -> MTT flattening + lock-depth preservation
#assert_no_axioms FX1Poly.Tier0.fitchToMtt
#assert_no_axioms FX1Poly.Tier0.mttToFitch
#assert_no_axioms FX1Poly.Tier0.lockCount_mapHyp
#assert_no_axioms FX1Poly.Tier0.lockCount_append
#assert_no_axioms FX1Poly.Tier0.fitchToMtt_lockCount
#assert_no_axioms FX1Poly.Tier0.dual_fitchToMtt_lockCount

-- The MTT context round trip (the splitting/joining bijection — discharges hasMttContextRoundTrip)
#assert_no_axioms FX1Poly.Tier0.appendEmptyRight
#assert_no_axioms FX1Poly.Tier0.prependZone
#assert_no_axioms FX1Poly.Tier0.prependZone_ne_nil
#assert_no_axioms FX1Poly.Tier0.mttToFitch_hyp
#assert_no_axioms FX1Poly.Tier0.mttToFitch_ne_nil
#assert_no_axioms FX1Poly.Tier0.prependZone_compose
#assert_no_axioms FX1Poly.Tier0.mttToFitch_mapHyp_append
#assert_no_axioms FX1Poly.Tier0.mttToFitch_fitchToMtt

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMttContextRoundTrip
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMultiModePresentation
#assert_no_axioms FX1Poly.Tier0.fxMode_hasTermLevelTranslation
#assert_no_axioms FX1Poly.Tier0.fxMode_hasBiequivalenceStrength
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelLockFibration

end FX1PolyAudit
