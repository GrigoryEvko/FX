import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TaggedSwapChain

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/TaggedSwapChain — zero-axiom gate

Per-declaration zero-axiom gate for the tagged chain layer: the projection zip, the
tagged swap tag-list shape and two-sided determinacy, the one-tagged-swap relation with
its symmetry and closure inclusion, the tagged chain with its groupoid operations, and
the closure identification in both directions.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.taggedListEqOfProjectionsEq
#assert_no_axioms FX1Poly.Polygraph.TaggedSpineAtomSwap.tagListShape
#assert_no_axioms FX1Poly.Polygraph.TaggedSpineAtomSwap.rhsDetermined
#assert_no_axioms FX1Poly.Polygraph.TaggedSpineAtomSwap.lhsDetermined
#assert_no_axioms FX1Poly.Polygraph.OneTaggedAdjacentSwap
#assert_no_axioms FX1Poly.Polygraph.OneTaggedAdjacentSwap.symm
#assert_no_axioms FX1Poly.Polygraph.OneTaggedAdjacentSwap.toTaggedTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.OneTaggedAdjacentSwapChain
#assert_no_axioms FX1Poly.Polygraph.OneTaggedAdjacentSwapChain.single
#assert_no_axioms FX1Poly.Polygraph.OneTaggedAdjacentSwapChain.trans
#assert_no_axioms FX1Poly.Polygraph.OneTaggedAdjacentSwapChain.symm
#assert_no_axioms FX1Poly.Polygraph.OneTaggedAdjacentSwapChain.consCongr
#assert_no_axioms FX1Poly.Polygraph.OneTaggedAdjacentSwapChain.toTaggedTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.TaggedTraceEquiv.toOneTaggedAdjacentSwapChain
#assert_no_axioms FX1Poly.Polygraph.oneTaggedAdjacentSwapChain_iff_taggedTraceEquiv

end FX1PolyAudit
