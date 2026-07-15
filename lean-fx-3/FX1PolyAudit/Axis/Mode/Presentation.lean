import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Presentation

/-! # FX1PolyAudit/AuditAxisModePresentation — zero-axiom gate for mode-27

Per-declaration zero-axiom gate for `mode-27` (`FX1Poly/Axis/Mode/Presentation.lean`): the three modal-context
presentations (MTT / Fitch / dual-context) + their depth measures, the Fitch ↔ dual-context bijection, the
Fitch → MTT flattening + lock-depth preservation, the tri-presentation depth agreement, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The three context representations + depth measures
#assert_no_axioms FX1Poly.Axis.MttEntry
#assert_no_axioms FX1Poly.Axis.MttContext.lockCount
#assert_no_axioms FX1Poly.Axis.FitchContext.lockDepth
#assert_no_axioms FX1Poly.Axis.DualContext

-- The Fitch <-> dual-context bijection (Pfenning-Davies = single-lock Fitch)
#assert_no_axioms FX1Poly.Axis.dualToFitch
#assert_no_axioms FX1Poly.Axis.fitchToDual
#assert_no_axioms FX1Poly.Axis.fitchToDual_dualToFitch
#assert_no_axioms FX1Poly.Axis.dualToFitch_fitchToDual
#assert_no_axioms FX1Poly.Axis.dualToFitch_lockDepth

-- The Fitch -> MTT flattening + lock-depth preservation
#assert_no_axioms FX1Poly.Axis.fitchToMtt
#assert_no_axioms FX1Poly.Axis.mttToFitch
#assert_no_axioms FX1Poly.Axis.lockCount_mapHyp
#assert_no_axioms FX1Poly.Axis.lockCount_append
#assert_no_axioms FX1Poly.Axis.fitchToMtt_lockCount
#assert_no_axioms FX1Poly.Axis.dual_fitchToMtt_lockCount

-- The MTT context round trip (the splitting/joining bijection — discharges hasMttContextRoundTrip)
#assert_no_axioms FX1Poly.Axis.appendEmptyRight
#assert_no_axioms FX1Poly.Axis.prependZone
#assert_no_axioms FX1Poly.Axis.prependZone_ne_nil
#assert_no_axioms FX1Poly.Axis.mttToFitch_hyp
#assert_no_axioms FX1Poly.Axis.mttToFitch_ne_nil
#assert_no_axioms FX1Poly.Axis.prependZone_compose
#assert_no_axioms FX1Poly.Axis.mttToFitch_mapHyp_append
#assert_no_axioms FX1Poly.Axis.mttToFitch_fitchToMtt

-- The term-level translation (box / unbox / let-box, discharges hasTermLevelTranslation)
#assert_no_axioms FX1Poly.Axis.FitchModalTerm
#assert_no_axioms FX1Poly.Axis.MttModalTerm
#assert_no_axioms FX1Poly.Axis.fitchToMttTerm
#assert_no_axioms FX1Poly.Axis.mttToFitchTerm
#assert_no_axioms FX1Poly.Axis.fitchToMttTerm_unbox
#assert_no_axioms FX1Poly.Axis.mttToFitchTerm_modElim
#assert_no_axioms FX1Poly.Axis.FitchModalTerm.boxCount
#assert_no_axioms FX1Poly.Axis.MttModalTerm.modCount
#assert_no_axioms FX1Poly.Axis.fitchToMttTerm_modCount
#assert_no_axioms FX1Poly.Axis.mttToFitchTerm_boxCount

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasMttContextRoundTrip
#assert_no_axioms FX1Poly.Axis.fxMode_hasMultiModePresentation
#assert_no_axioms FX1Poly.Axis.fxMode_hasTermLevelTranslation
#assert_no_axioms FX1Poly.Axis.fxMode_hasBiequivalenceStrength
#assert_no_axioms FX1Poly.Axis.fxMode_hasKernelLockFibration

end FX1PolyAudit
