import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapExtractionTransport

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SwapExtractionTransport — zero-axiom gate

Per-declaration zero-axiom gate for recognizer totality-on-a-witness and the whole-trace
transport lemmas across one adjacent swap.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.recognizeAdjacentSwap_firesOnWitness
#assert_no_axioms FX1Poly.Polygraph.recognizeReverseAdjacentSwap_firesOnWitness
#assert_no_axioms FX1Poly.Polygraph.SpineAtomSwap.targetIsExtractionOfSource
#assert_no_axioms FX1Poly.Polygraph.SpineAtomSwap.sourceIsExtractionOfTarget

end FX1PolyAudit
