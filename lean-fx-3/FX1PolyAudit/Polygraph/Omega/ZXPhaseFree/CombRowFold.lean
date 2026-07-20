import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CombRowFold

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.CombRowFold — zero-axiom gate (the
moving-position single-row comb-row fold: unset-bit traversal, span fires, and the
prefix-shift identity)

Per-declaration zero-axiom gate for the comb-row-fold round: the fold source and
its r19 pin, the two fresh comb-layer expansion pins (`[false, true]` /
`[true, false, true]`), the four single-row span fires, the two regression
re-exposures, the fresh unset-bit traversal (`zxqCombTraversalFalseTrue`) with its
fire and fused-output span pin, the proven comb prefix-shift identity
(`zxqCombPrefixShift`) with its leading-unset corollary, the three live content
markers, and the owner-false general-fold marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`, `WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob;
AuditAll registration is a later round's bookkeeping (AuditAll untouched per this
round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqFoldSource
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqFoldSourceTwoBitPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqFalseTrueCombLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqTrueFalseTrueCombLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqFoldSpanPinOneBit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqFoldSpanPinTwoBit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqFoldSpanPinFalseTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqFoldSpanPinTrueFalseTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqCombTraversalOneBit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqCombTraversalTwoBit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqCombTraversalFalseTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqCombTraversalFalseTrueFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqFalseTrueOutputFusedSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqCombPrefixShift
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqFalseLeadCombStructure
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqHasUnsetBitTraversal
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqHasSingleRowSpanFires
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqHasPrefixShiftIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxqHasGeneralCombFold

end FX1PolyAudit
