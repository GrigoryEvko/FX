import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ReverseSwapRecognizer

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ReverseSwapRecognizer — zero-axiom gate

Per-declaration zero-axiom gate for the reverse adjacent-swap certificate, its soundness,
and the reverse recognizer.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ReverseAdjacentSwapWitness.movedFront
#assert_no_axioms FX1Poly.Polygraph.ReverseAdjacentSwapWitness.stayedBehind
#assert_no_axioms FX1Poly.Polygraph.ReverseAdjacentSwapWitness.toSwap
#assert_no_axioms FX1Poly.Polygraph.recognizeReverseAdjacentSwap

end FX1PolyAudit
