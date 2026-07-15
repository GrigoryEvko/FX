import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Session

/-! # FX1PolyAudit/Axis/Mode/SessionMore — zero-axiom gate for mode-25 (part 2 of 2)

Per-declaration zero-axiom gate for `mode-25` (`FX1Poly/Axis/Mode/Session.lean`), continued from
`Session.lean`: the arbitrary-N multiparty projection (communication fragment + third-party skip + bipartite
duality), the global CHOICE + plain-merge projection, delegation (higher-order sessions), and the honesty
markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Arbitrary-N multiparty projection (communication fragment + third-party skip + bipartite duality)
#assert_no_axioms FX1Poly.Axis.GlobalType
#assert_no_axioms FX1Poly.Axis.GlobalType.projectTo
#assert_no_axioms FX1Poly.Axis.GlobalType.projectTo_sender
#assert_no_axioms FX1Poly.Axis.GlobalType.projectTo_receiver
#assert_no_axioms FX1Poly.Axis.GlobalType.projectTo_skip
#assert_no_axioms FX1Poly.Axis.GlobalType.isBipartite
#assert_no_axioms FX1Poly.Axis.GlobalType.projectTo_dual_of_bipartite

-- Global CHOICE + plain-merge projection (closes hasSessionMultipartyProjection)
#assert_no_axioms FX1Poly.Axis.MpstGlobal
#assert_no_axioms FX1Poly.Axis.MpstBranches
#assert_no_axioms FX1Poly.Axis.MpstGlobal.projectMpst
#assert_no_axioms FX1Poly.Axis.MpstBranches.projectSelect
#assert_no_axioms FX1Poly.Axis.MpstBranches.projectOffer
#assert_no_axioms FX1Poly.Axis.MpstBranches.projectMerge
#assert_no_axioms FX1Poly.Axis.MpstBranches.allAgreeWith
#assert_no_axioms FX1Poly.Axis.MpstGlobal.projectMpst_decider
#assert_no_axioms FX1Poly.Axis.MpstGlobal.projectMpst_chooser
#assert_no_axioms FX1Poly.Axis.MpstGlobal.projectMpst_third
#assert_no_axioms FX1Poly.Axis.MpstBranches.projectMerge_eq_of_agree
#assert_no_axioms FX1Poly.Axis.exampleThreePartyGlobal
#assert_no_axioms FX1Poly.Axis.exampleThreeParty_observer_merges
#assert_no_axioms FX1Poly.Axis.exampleThreeParty_observer_agrees
#assert_no_axioms FX1Poly.Axis.exampleThreeParty_decider_selects

-- Delegation — higher-order sessions (channel over channel)
#assert_no_axioms FX1Poly.Axis.DelegatingSession
#assert_no_axioms FX1Poly.Axis.DelegatingSession.dual
#assert_no_axioms FX1Poly.Axis.DelegatingSession.dual_dDelegate
#assert_no_axioms FX1Poly.Axis.DelegatingSession.dual_dAccept
#assert_no_axioms FX1Poly.Axis.DelegatingSession.dual_dual
#assert_no_axioms FX1Poly.Axis.DelegatingSession.isHigherOrder
#assert_no_axioms FX1Poly.Axis.DelegatingSession.dual_isHigherOrder

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasSessionTwoCellCoherence
#assert_no_axioms FX1Poly.Axis.fxMode_hasSessionMultipartyProjection
#assert_no_axioms FX1Poly.Axis.fxMode_hasSessionWidthSubtyping
#assert_no_axioms FX1Poly.Axis.fxMode_hasSessionRecursionScoping
#assert_no_axioms FX1Poly.Axis.fxMode_hasSessionDelegation
#assert_no_axioms FX1Poly.Axis.fxMode_hasSessionKernelProtocolFibration

end FX1PolyAudit
