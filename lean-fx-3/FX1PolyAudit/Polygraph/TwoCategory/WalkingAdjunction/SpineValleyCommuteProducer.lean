import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteProducer

/-! # FX1PolyAudit/…/SpineValleyCommuteProducer — zero-axiom gate

Per-declaration zero-axiom gate for COMMUTE bricks 2+3 (the flat swap from the classifier + the producer): the
seed cup/cap arities (`cupAtom_generatorDom_length_zero`, `cupAtom_generatorCod_length_two`,
`capAtom_generatorDom_length_two`), the Type-valued disjoint-window factorization
(`adjunctionContextsFactorData_of_disjointWindows`), the combined pair data
(`adjunctionCommutePairData_of_disjointWindows`), the sign/`windowGap` derivation
(`disjointWindows_directedOffset_ge_two`), and the COMMUTE producer (`commuteCellDescentStepRight`).  Every
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`.
Auditing the producer transitively covers the private `natAddLeftCancel`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupAtom_generatorDom_length_zero
#assert_no_axioms FX1Poly.Polygraph.cupAtom_generatorCod_length_two
#assert_no_axioms FX1Poly.Polygraph.capAtom_generatorDom_length_two
#assert_no_axioms FX1Poly.Polygraph.adjunctionContextsFactorData_of_disjointWindows
#assert_no_axioms FX1Poly.Polygraph.adjunctionCommutePairData_of_disjointWindows
#assert_no_axioms FX1Poly.Polygraph.disjointWindows_directedOffset_ge_two
#assert_no_axioms FX1Poly.Polygraph.commuteCellDescentStepRight
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyCommuteProducer

end FX1PolyAudit
