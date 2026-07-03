import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FramedSpineChain

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/FramedSpineChain — zero-axiom gate

Per-declaration zero-axiom gate for the boundary-coherent spine chain (FREE-1): the chain
datatype, the total readback, the readback-spine section theorem, and the assembly pieces.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.readback
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.readback_spine
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.append
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.singleton
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasFramedSpineChain

end FX1PolyAudit
