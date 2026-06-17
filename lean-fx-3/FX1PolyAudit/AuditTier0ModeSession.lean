import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Session

/-! # FX1PolyAudit/AuditTier0ModeSession — zero-axiom gate for mode-25

Per-declaration zero-axiom gate for `mode-25` (`FX1Poly/Tier0/Mode/Session.lean`): the involution structure, the
session protocols + duality + the self-inverse `dual_dual`, the sub-protocol precongruence + reflexivity +
duality-monotonicity, the communication advance + session fidelity, deadlock-freedom, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Involutions
#assert_no_axioms FX1Poly.Tier0.Involution

-- Session protocols + duality (the self-inverse 2-cell)
#assert_no_axioms FX1Poly.Tier0.SessionProtocol
#assert_no_axioms FX1Poly.Tier0.SessionProtocol.dual
#assert_no_axioms FX1Poly.Tier0.SessionProtocol.dual_dual
#assert_no_axioms FX1Poly.Tier0.sessionDualityInvolution

-- The sub-protocol order (the 1-cell order)
#assert_no_axioms FX1Poly.Tier0.SessionSubtype
#assert_no_axioms FX1Poly.Tier0.SessionSubtype.refl
#assert_no_axioms FX1Poly.Tier0.SessionSubtype.dual_monotone

-- Communication step + session fidelity
#assert_no_axioms FX1Poly.Tier0.SessionAdvance
#assert_no_axioms FX1Poly.Tier0.SessionAdvance.dual_fidelity

-- Deadlock-freedom
#assert_no_axioms FX1Poly.Tier0.SessionProtocol.canAdvance
#assert_no_axioms FX1Poly.Tier0.SessionProtocol.canAdvance_progress
#assert_no_axioms FX1Poly.Tier0.SessionProtocol.deadlockFree

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSessionTwoCellCoherence
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSessionMultipartyProjection
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSessionWidthSubtyping
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSessionRecursionScoping
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSessionKernelProtocolFibration

end FX1PolyAudit
