import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCommuteProducer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyCommuteProducer — zero-axiom gate (FC-3 r6, B2)

Per-declaration zero-axiom gate for the RIGHT-of string COMMUTE producer: the seed cup/cap generator arities, the
directed-offset bound, the pair-data bundle and its builder, the producer, and the honesty marker.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCupAtom_generatorDom_length_zero
#assert_no_axioms FX1Poly.Polygraph.stringCupAtom_generatorCod_length_two
#assert_no_axioms FX1Poly.Polygraph.stringCapAtom_generatorDom_length_two
#assert_no_axioms FX1Poly.Polygraph.stringDisjointWindows_directedOffset_ge_two
#assert_no_axioms FX1Poly.Polygraph.StringCommutePairData
#assert_no_axioms FX1Poly.Polygraph.stringCommutePairData_of_disjointWordWindows
#assert_no_axioms FX1Poly.Polygraph.stringCommuteCellDescentStepRight
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringValleyCommuteProducer

end FX1PolyAudit
