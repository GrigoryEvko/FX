import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Session

/-! # FX1PolyAudit/Axis/Mode/Session — zero-axiom gate for mode-25 (part 1 of 2)

Per-declaration zero-axiom gate for `mode-25` (`FX1Poly/Axis/Mode/Session.lean`): the involution structure, the
session protocols + duality + the self-inverse `dual_dual`, the sub-protocol precongruence + reflexivity +
duality-monotonicity, the communication advance + session fidelity, deadlock-freedom, well-scoped recursion,
the duality 2-cell coherence, the 2-party global-to-local projection, and the n-ary labelled choice + Gay-Hole
width subtyping. The arbitrary-N multiparty projection, delegation, and honesty markers continue in
`SessionMore.lean`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Involutions
#assert_no_axioms FX1Poly.Axis.Involution

-- Session protocols + duality (the self-inverse 2-cell)
#assert_no_axioms FX1Poly.Axis.SessionProtocol
#assert_no_axioms FX1Poly.Axis.SessionProtocol.dual
#assert_no_axioms FX1Poly.Axis.SessionProtocol.dual_dual
#assert_no_axioms FX1Poly.Axis.sessionDualityInvolution

-- The sub-protocol order (the 1-cell order)
#assert_no_axioms FX1Poly.Axis.SessionSubtype
#assert_no_axioms FX1Poly.Axis.SessionSubtype.refl
#assert_no_axioms FX1Poly.Axis.SessionSubtype.dual_monotone

-- Communication step + session fidelity
#assert_no_axioms FX1Poly.Axis.SessionAdvance
#assert_no_axioms FX1Poly.Axis.SessionAdvance.dual_fidelity

-- Deadlock-freedom
#assert_no_axioms FX1Poly.Axis.SessionProtocol.canAdvance
#assert_no_axioms FX1Poly.Axis.SessionProtocol.canAdvance_progress
#assert_no_axioms FX1Poly.Axis.SessionProtocol.deadlockFree

-- Well-scoped recursion (discharges hasSessionRecursionScoping)
#assert_no_axioms FX1Poly.Axis.SessionProtocol.wellScopedAt
#assert_no_axioms FX1Poly.Axis.SessionProtocol.wellScoped
#assert_no_axioms FX1Poly.Axis.SessionProtocol.dual_wellScopedAt
#assert_no_axioms FX1Poly.Axis.SessionProtocol.dual_wellScoped

-- Duality as a coherent 2-cell (discharges hasSessionTwoCellCoherence)
#assert_no_axioms FX1Poly.Axis.SessionSubtype.dual_reflect
#assert_no_axioms FX1Poly.Axis.SessionSubtype.dual_iff

-- The 2-party global-to-local projection (partial multiparty)
#assert_no_axioms FX1Poly.Axis.GlobalStep
#assert_no_axioms FX1Poly.Axis.GlobalProtocol
#assert_no_axioms FX1Poly.Axis.GlobalProtocol.projectA
#assert_no_axioms FX1Poly.Axis.GlobalProtocol.projectB
#assert_no_axioms FX1Poly.Axis.GlobalProtocol.projectB_eq_dual_projectA

-- n-ary labelled choice + Gay-Hole width subtyping (discharges hasSessionWidthSubtyping)
#assert_no_axioms FX1Poly.Axis.WidthSession
#assert_no_axioms FX1Poly.Axis.ChoiceList
#assert_no_axioms FX1Poly.Axis.WidthSession.dual
#assert_no_axioms FX1Poly.Axis.ChoiceList.dualList
#assert_no_axioms FX1Poly.Axis.WidthSession.dual_dual
#assert_no_axioms FX1Poly.Axis.ChoiceList.dualList_dualList
#assert_no_axioms FX1Poly.Axis.WidthSubtype
#assert_no_axioms FX1Poly.Axis.widthSubtype_refl
#assert_no_axioms FX1Poly.Axis.widthSelectRefl
#assert_no_axioms FX1Poly.Axis.widthBranchRefl
#assert_no_axioms FX1Poly.Axis.widthSubtype_dual_antitone
#assert_no_axioms FX1Poly.Axis.widthCompatibleClient

end FX1PolyAudit
