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

-- Well-scoped recursion (discharges hasSessionRecursionScoping)
#assert_no_axioms FX1Poly.Tier0.SessionProtocol.wellScopedAt
#assert_no_axioms FX1Poly.Tier0.SessionProtocol.wellScoped
#assert_no_axioms FX1Poly.Tier0.SessionProtocol.dual_wellScopedAt
#assert_no_axioms FX1Poly.Tier0.SessionProtocol.dual_wellScoped

-- Duality as a coherent 2-cell (discharges hasSessionTwoCellCoherence)
#assert_no_axioms FX1Poly.Tier0.SessionSubtype.dual_reflect
#assert_no_axioms FX1Poly.Tier0.SessionSubtype.dual_iff

-- The 2-party global-to-local projection (partial multiparty)
#assert_no_axioms FX1Poly.Tier0.GlobalStep
#assert_no_axioms FX1Poly.Tier0.GlobalProtocol
#assert_no_axioms FX1Poly.Tier0.GlobalProtocol.projectA
#assert_no_axioms FX1Poly.Tier0.GlobalProtocol.projectB
#assert_no_axioms FX1Poly.Tier0.GlobalProtocol.projectB_eq_dual_projectA

-- n-ary labelled choice + Gay-Hole width subtyping (discharges hasSessionWidthSubtyping)
#assert_no_axioms FX1Poly.Tier0.WidthSession
#assert_no_axioms FX1Poly.Tier0.ChoiceList
#assert_no_axioms FX1Poly.Tier0.WidthSession.dual
#assert_no_axioms FX1Poly.Tier0.ChoiceList.dualList
#assert_no_axioms FX1Poly.Tier0.WidthSession.dual_dual
#assert_no_axioms FX1Poly.Tier0.ChoiceList.dualList_dualList
#assert_no_axioms FX1Poly.Tier0.WidthSubtype
#assert_no_axioms FX1Poly.Tier0.widthSubtype_refl
#assert_no_axioms FX1Poly.Tier0.widthSelectRefl
#assert_no_axioms FX1Poly.Tier0.widthBranchRefl
#assert_no_axioms FX1Poly.Tier0.widthSubtype_dual_antitone
#assert_no_axioms FX1Poly.Tier0.widthCompatibleClient

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
