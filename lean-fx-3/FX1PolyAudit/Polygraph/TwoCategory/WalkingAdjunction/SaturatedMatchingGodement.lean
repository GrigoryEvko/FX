import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingGodement

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingGodement — zero-axiom gate (mode-9 keystone)

Per-declaration zero-axiom gate for the matching-carrier Godement residual reduction: the fold-decomposition
engine (`runMatchingCell`, `processSpine_spineDiff`), the two-block commutation core `MatchingGodementCommute`,
the reduction `matchingGodementInvariant_of_commute`, and the keystone soundness re-gated on the two-block core.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- the fold-decomposition engine
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell
#assert_no_axioms FX1Poly.Polygraph.processSpine_spineDiff

-- ★ the two-block commutation core + the reduction of the keystone's raw godementInvariant to it
#assert_no_axioms FX1Poly.Polygraph.MatchingGodementCommute
#assert_no_axioms FX1Poly.Polygraph.matchingGodementInvariant_of_commute

-- the keystone soundness + canonicalization re-gated on the two-block core
#assert_no_axioms FX1Poly.Polygraph.saturatedConv_matchingOf_eq_of_commute
#assert_no_axioms FX1Poly.Polygraph.saturatedMatchingCanonicalization_ofCommute

-- ★ renaming-invariance of the matching extract — the partition-view half, CLOSED
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes
#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_eq_of_connectivityView
#assert_no_axioms FX1Poly.Polygraph.MatchingRenameRel
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_of_matchingRenameRel

-- ★ residual 1 fully reduced to the renaming-witness construction
#assert_no_axioms FX1Poly.Polygraph.MatchingGodementSwapRenameable
#assert_no_axioms FX1Poly.Polygraph.matchingGodementCommute_of_swapRenameable
#assert_no_axioms FX1Poly.Polygraph.saturatedConv_matchingOf_eq_of_swapRenameable

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingGodementFoldDecomposition
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingGodementReducedToBlockCommute
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingExtractRenameInvariance
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingGodementReducedToSwapRenameable
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingBlockCommuteProof

end FX1PolyAudit
