import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Session

/-! # FX1PolyAudit/Tier0/Mode/SessionMore — zero-axiom gate for mode-25 (part 2 of 2)

Per-declaration zero-axiom gate for `mode-25` (`FX1Poly/Tier0/Mode/Session.lean`), continued from
`Session.lean`: the arbitrary-N multiparty projection (communication fragment + third-party skip + bipartite
duality), the global CHOICE + plain-merge projection, delegation (higher-order sessions), and the honesty
markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Arbitrary-N multiparty projection (communication fragment + third-party skip + bipartite duality)
#assert_no_axioms FX1Poly.Tier0.GlobalType
#assert_no_axioms FX1Poly.Tier0.GlobalType.projectTo
#assert_no_axioms FX1Poly.Tier0.GlobalType.projectTo_sender
#assert_no_axioms FX1Poly.Tier0.GlobalType.projectTo_receiver
#assert_no_axioms FX1Poly.Tier0.GlobalType.projectTo_skip
#assert_no_axioms FX1Poly.Tier0.GlobalType.isBipartite
#assert_no_axioms FX1Poly.Tier0.GlobalType.projectTo_dual_of_bipartite

-- Global CHOICE + plain-merge projection (closes hasSessionMultipartyProjection)
#assert_no_axioms FX1Poly.Tier0.MpstGlobal
#assert_no_axioms FX1Poly.Tier0.MpstBranches
#assert_no_axioms FX1Poly.Tier0.MpstGlobal.projectMpst
#assert_no_axioms FX1Poly.Tier0.MpstBranches.projectSelect
#assert_no_axioms FX1Poly.Tier0.MpstBranches.projectOffer
#assert_no_axioms FX1Poly.Tier0.MpstBranches.projectMerge
#assert_no_axioms FX1Poly.Tier0.MpstBranches.allAgreeWith
#assert_no_axioms FX1Poly.Tier0.MpstGlobal.projectMpst_decider
#assert_no_axioms FX1Poly.Tier0.MpstGlobal.projectMpst_chooser
#assert_no_axioms FX1Poly.Tier0.MpstGlobal.projectMpst_third
#assert_no_axioms FX1Poly.Tier0.MpstBranches.projectMerge_eq_of_agree
#assert_no_axioms FX1Poly.Tier0.exampleThreePartyGlobal
#assert_no_axioms FX1Poly.Tier0.exampleThreeParty_observer_merges
#assert_no_axioms FX1Poly.Tier0.exampleThreeParty_observer_agrees
#assert_no_axioms FX1Poly.Tier0.exampleThreeParty_decider_selects

-- Delegation — higher-order sessions (channel over channel)
#assert_no_axioms FX1Poly.Tier0.DelegatingSession
#assert_no_axioms FX1Poly.Tier0.DelegatingSession.dual
#assert_no_axioms FX1Poly.Tier0.DelegatingSession.dual_dDelegate
#assert_no_axioms FX1Poly.Tier0.DelegatingSession.dual_dAccept
#assert_no_axioms FX1Poly.Tier0.DelegatingSession.dual_dual
#assert_no_axioms FX1Poly.Tier0.DelegatingSession.isHigherOrder
#assert_no_axioms FX1Poly.Tier0.DelegatingSession.dual_isHigherOrder

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSessionTwoCellCoherence
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSessionMultipartyProjection
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSessionWidthSubtyping
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSessionRecursionScoping
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSessionDelegation
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSessionKernelProtocolFibration

end FX1PolyAudit
