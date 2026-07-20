import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Dpo.DpoRewriting

/-! # FX1PolyAudit/Polygraph/Dpo/DpoRewriting — zero-axiom gate
    (WP-DPO-ENGINE brick: double-pushout hypergraph rewriting)

Per-declaration zero-axiom gate for the DPO single-step rewrite engine: the carrier
(`Hyperedge`/`Hypergraph`/`DpoRule`/`Match`), the cons-only list + edge primitives,
the canonical-form graph decision `canonicalHypergraphBeq` with soundness, the
well-formedness predicates, the pushout-complement (`pushoutComplementExists` /
`dpoDeleteContext`), the union-find pushout (`dpgGlueLinks` / `dpoGluePushout`), the
single-step decision `dpoRewriteAt` / `decideRewritesTo`, the `DpoRewriteStep`
relation with `dpoRewriteStepSound` + the `none`-refutation half, the concrete
example + fires, the capability markers, and the three walls.

Walls (`false`): multi-step reachability is undecidable
(`dpgHasGeneralReachability`); confluence needs an undecidable termination hypothesis
(`dpgHasConfluence`); pushout-complement uniqueness fails for non-mono matches
(`dpgHasPushoutComplementUniqueness`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Dpo.Hyperedge
#assert_no_axioms FX1Poly.Polygraph.Dpo.Hyperedge.mk
#assert_no_axioms FX1Poly.Polygraph.Dpo.Hypergraph
#assert_no_axioms FX1Poly.Polygraph.Dpo.Hypergraph.mk
#assert_no_axioms FX1Poly.Polygraph.Dpo.DpoRule
#assert_no_axioms FX1Poly.Polygraph.Dpo.DpoRule.mk
#assert_no_axioms FX1Poly.Polygraph.Dpo.Match
#assert_no_axioms FX1Poly.Polygraph.Dpo.Match.mk
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgAppendNat
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgAppendEdge
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgNth
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgRangeFrom
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgRange
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgLt
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgInjective
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeRelabel
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgesRelabel
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeBeq
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeListBeq
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeLe
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeInsert
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeSort
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeMemBool
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeRemoveThose
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgAllEndpoints
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgCanonicalize
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgHypergraphBeq
#assert_no_axioms FX1Poly.Polygraph.Dpo.canonicalHypergraphBeq
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEndpointsValid
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgesValid
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgHypergraphWellFormed
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgRuleWellFormed
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgMatchWellFormed
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgInterfaceImageEdges
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgDeletedLeftEdges
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgDeletedHostEdges
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpoDeleteContext
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgSiftNotIn
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgDeletedLeftNodes
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgDeletedHostNodes
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgAllNotMem
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgesAvoidNodes
#assert_no_axioms FX1Poly.Polygraph.Dpo.pushoutComplementExists
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgBuildGlue
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgGlueLinks
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpoGluePushout
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpoRewriteAt
#assert_no_axioms FX1Poly.Polygraph.Dpo.decideRewritesTo
#assert_no_axioms FX1Poly.Polygraph.Dpo.DpoRewriteStep
#assert_no_axioms FX1Poly.Polygraph.Dpo.DpoRewriteStep.ofRewrite
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeBeqRefl
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeListBeqRefl
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgHypergraphBeqRefl
#assert_no_axioms FX1Poly.Polygraph.Dpo.canonicalHypergraphBeqRefl
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeBeqEq
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgEdgeListBeqEq
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgHypergraphBeqEq
#assert_no_axioms FX1Poly.Polygraph.Dpo.canonicalHypergraphBeqSound
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpoRewriteStepSound
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpoRewriteNoneRefutes
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgHostPath
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgRelabelRule
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgMatchAtZeroOne
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgDeleteNodeRule
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgResultAtZeroOne
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgFireComplementExistsGood
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgFireContextDropsMatchedEdge
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgFireInterfaceNodeZeroGlued
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgFireInterfaceNodeOneGlued
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgFireRewriteDecidesTrue
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgFireRewriteMatchesHandwritten
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgFireWrongResultDecidesFalse
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgFireDanglingComplementNone
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgFireDanglingComplementFalse
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgFireDanglingDecidesFalse
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgFireRewriteStep
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgHasSingleStepDecision
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgHasMonoMatchComplementExists
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgHasGeneralReachability
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgHasConfluence
#assert_no_axioms FX1Poly.Polygraph.Dpo.dpgHasPushoutComplementUniqueness

end FX1PolyAudit
