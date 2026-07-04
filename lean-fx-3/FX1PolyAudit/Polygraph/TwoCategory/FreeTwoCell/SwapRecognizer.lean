import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapRecognizer

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SwapRecognizer — zero-axiom gate

Per-declaration zero-axiom gate for the adjacent-swap certificate, its soundness, and the
computable recognizer.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.AdjacentSwapWitness.firstAfterSwap
#assert_no_axioms FX1Poly.Polygraph.AdjacentSwapWitness.secondAfterSwap
#assert_no_axioms FX1Poly.Polygraph.AdjacentSwapWitness.toSwap
#assert_no_axioms FX1Poly.Polygraph.recognizeAdjacentSwap

end FX1PolyAudit
