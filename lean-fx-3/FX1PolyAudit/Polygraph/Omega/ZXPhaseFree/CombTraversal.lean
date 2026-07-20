import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CombTraversal

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.CombTraversal — zero-axiom gate
(the state-walk router, the feeding-column cells and collapse, and one full comb
traversal)

Per-declaration zero-axiom gate for the comb-traversal round: the literal-arity
helpers, the state-walk staircase (`zxuStateWalk`, general in the gap width) with
its walk-layer well-formedness / cod-arity lemmas, fires and span pins; the
feeding-column cells (`zxuStateForkOnCarrier`, `zxuStateMergeOnCarrier`, the
mirror `zxuStateMergeAbsorbsRight`) with fires and span pins; the feeding-column
collapse (`zxuFeedColumnCollapse`); the carrier birth-and-death and the full comb
traversal (`zxuCombTraversalOneBit`) with their span pins; the live content
markers and the owner-false general-identity-absorb marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`, `funext`.  Built by the
FX1PolyAudit lib glob; AuditAll registration is a later round's bookkeeping
(AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuTwoSplitLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuTwoSplitRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuCreateLeftLayer
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuCreateRightLayer
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkLhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkRhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuCreateLeftLayerDomArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuCreateLeftLayerCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuWalkHeadCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkLayersWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkLayersCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkLhsWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalk
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkOneFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkTwoFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkThreeFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkOneSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkTwoSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateWalkThreeSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateForkOnCarrier
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateMergeOnCarrier
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateForkOnCarrierFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateMergeOnCarrierFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateForkOnCarrierSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateMergeOnCarrierSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateMergeAbsorbsRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuStateMergeAbsorbsRightSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuFeedColumnCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuFeedColumnCollapseSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuCarrierBirthDeath
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuCombTraversalOneBit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuCombTraversalOneBitSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuCarrierBirthDeathSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuHasStateWalkRouter
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuHasFeedingColumnCells
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuHasFeedingColumnCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuHasFullCombTraversal
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxuHasGeneralIdentityAbsorb

end FX1PolyAudit
