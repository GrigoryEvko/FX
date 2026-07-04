import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FarCommutation

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/FarCommutation — zero-axiom gate

Per-declaration zero-axiom gate for the far-commutation layer: the tail-replacement
primitive and the two packaged exchange squares.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.TaggedSpineAtomSwap.replaceRest
#assert_no_axioms FX1Poly.Polygraph.OneTaggedAdjacentSwapChain.exchangeHeadSwapPastDeepChain
#assert_no_axioms FX1Poly.Polygraph.OneTaggedAdjacentSwapChain.exchangeReversedHeadSwapPastDeepChain

end FX1PolyAudit
