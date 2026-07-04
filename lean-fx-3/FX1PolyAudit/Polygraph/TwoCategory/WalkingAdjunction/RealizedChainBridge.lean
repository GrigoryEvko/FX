import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.RealizedChainBridge

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/RealizedChainBridge — zero-axiom gate

Per-declaration zero-axiom gate for the realized-chain ↔ framed-chain bridge: the two
cast-free translations, the readback agreements, the atom-list round trips, and the
cell↔chain bridge at `TwoCellConvFull`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RealizedSpineChain.toFramedSpineChain
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.toRealizedSpineChain
#assert_no_axioms FX1Poly.Polygraph.RealizedSpineChain.toFramedSpineChain_readback
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.toRealizedSpineChain_readback
#assert_no_axioms FX1Poly.Polygraph.RealizedSpineChain.toFramedSpineChain_spine
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.toRealizedSpineChain_atoms
#assert_no_axioms FX1Poly.Polygraph.RealizedSpineChain.chainToCell_convFull_ofSpineEq

end FX1PolyAudit
