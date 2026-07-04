import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapInversion

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SwapInversion — zero-axiom gate

Per-declaration zero-axiom gate for the swap inversions (through the forward and reverse
witnesses), witness uniqueness, and swap determinacy.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.AdjacentSwapWitness.inertPathsCoincide
#assert_no_axioms FX1Poly.Polygraph.ReverseAdjacentSwapWitness.inertPathsCoincide
#assert_no_axioms FX1Poly.Polygraph.AdjacentSwapWitness.firstAfterSwapCoincides
#assert_no_axioms FX1Poly.Polygraph.AdjacentSwapWitness.secondAfterSwapCoincides
#assert_no_axioms FX1Poly.Polygraph.ReverseAdjacentSwapWitness.movedFrontCoincides
#assert_no_axioms FX1Poly.Polygraph.ReverseAdjacentSwapWitness.stayedBehindCoincides
#assert_no_axioms FX1Poly.Polygraph.SpineAtomSwap.forwardInversion
#assert_no_axioms FX1Poly.Polygraph.SpineAtomSwap.reverseInversion
#assert_no_axioms FX1Poly.Polygraph.SpineAtomSwap.rhsDetermined
#assert_no_axioms FX1Poly.Polygraph.SpineAtomSwap.lhsDetermined

end FX1PolyAudit
