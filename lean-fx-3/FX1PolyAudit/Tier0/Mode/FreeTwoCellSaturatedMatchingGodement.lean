import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellSaturatedMatchingGodement

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellSaturatedMatchingGodement — zero-axiom gate (mode-9 keystone)

Per-declaration zero-axiom gate for the matching-carrier Godement residual reduction: the fold-decomposition
engine (`runMatchingCell`, `processSpine_spineDiff`), the two-block commutation core `MatchingGodementCommute`,
the reduction `matchingGodementInvariant_of_commute`, and the keystone soundness re-gated on the two-block core.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- the fold-decomposition engine
#assert_no_axioms FX1Poly.Tier0.runMatchingCell
#assert_no_axioms FX1Poly.Tier0.processSpine_spineDiff

-- ★ the two-block commutation core + the reduction of the keystone's raw godementInvariant to it
#assert_no_axioms FX1Poly.Tier0.MatchingGodementCommute
#assert_no_axioms FX1Poly.Tier0.matchingGodementInvariant_of_commute

-- the keystone soundness + canonicalization re-gated on the two-block core
#assert_no_axioms FX1Poly.Tier0.saturatedConv_matchingOf_eq_of_commute
#assert_no_axioms FX1Poly.Tier0.saturatedMatchingCanonicalization_ofCommute

-- ★ renaming-invariance of the matching extract — the partition-view half, CLOSED
#assert_no_axioms FX1Poly.Tier0.matchingBoundaryNodes
#assert_no_axioms FX1Poly.Tier0.matchingSameComponent
#assert_no_axioms FX1Poly.Tier0.extractDiagram_eq_of_connectivityView
#assert_no_axioms FX1Poly.Tier0.MatchingRenameRel
#assert_no_axioms FX1Poly.Tier0.extractDiagram_of_matchingRenameRel

-- honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingGodementFoldDecomposition
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingGodementReducedToBlockCommute
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingExtractRenameInvariance
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingBlockCommuteProof

end FX1PolyAudit
