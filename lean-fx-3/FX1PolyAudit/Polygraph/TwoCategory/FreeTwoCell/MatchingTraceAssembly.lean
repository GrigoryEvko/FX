import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingTraceAssembly

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingTraceAssembly — zero-axiom gate

Per-declaration zero-axiom gate for the cross-order trace assembly: the blockwise pair-map over a
trace concatenation, the per-block trace correspondences (order-2's alpha/beta traces are the
`blockRotate` images of order-1's), the combined reordered-trace correspondence, and the honesty
marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.listMapPairAppend
#assert_no_axioms FX1Poly.Polygraph.matchingCoreSwap_alphaTrace_blockRotate
#assert_no_axioms FX1Poly.Polygraph.matchingCoreSwap_betaTrace_blockRotate
#assert_no_axioms FX1Poly.Polygraph.matchingCoreSwap_joinEvents_blockRotate
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingTraceBlockRotateWitness

end FX1PolyAudit
