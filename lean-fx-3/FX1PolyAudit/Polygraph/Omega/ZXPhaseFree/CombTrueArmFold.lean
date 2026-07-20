import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CombTrueArmFold

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.CombTrueArmFold — zero-axiom gate
(the shared-copy-prefix carrier and its general fusion, the chain-fuse fires, the
single-row span fires, and the honest general-fold wall)

Per-declaration zero-axiom gate for the true-arm-fold round: the arithmetic
shifter, the copy-chain carrier and its single-cell WF, the general chain fusion
(`zxhChainFromFuse`) and free-copy-state fusion (`zxhFreeCopyStateFuses`), the
length-3 explicit pin, the four chain-fuse fires, the committed two-bit traversal
re-derived through the chain, the six span fires (three correlated pins plus two
discriminating FALSE controls plus the free-copy pin), the three live content
markers, and the owner-false general-fold marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`, `WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob;
AuditAll registration is a later round's bookkeeping (AuditAll untouched per this
round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhSuccSlideRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhChainFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhSpiderLayerWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhChainFromFuse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhFreeCopyState
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhFreeCopyStateFuses
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhLengthThreeChainLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhLengthThreeChainFuseFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhLengthFourChainFuseFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhStartTwoChainFuseFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhFreeCopyThreeFuseFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhTwoBitTraversalViaChain
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhFreeCopyThreeSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhTrueTrueTrueSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhTrueTrueTrueChainSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhTrueTrueTrueNotIndependentSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhTrueTrueTrueNotZeroSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhHasSharedCopyChainFusion
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhHasTwoBitViaChain
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhHasChainAndSpanFires
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxhHasGeneralSingleRowFold

end FX1PolyAudit
