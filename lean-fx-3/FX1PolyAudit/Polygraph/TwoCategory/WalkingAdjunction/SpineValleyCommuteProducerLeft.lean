import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteProducerLeft

/-! # FX1PolyAudit/…/SpineValleyCommuteProducerLeft — zero-axiom gate

Per-declaration zero-axiom gate for the COMMUTE producer's LEFT-of mirror (the second window a gap left of the
first): the Type-valued mirrored factorization (`adjunctionContextsFactorDataLeft_of_disjointWindows`), the
combined pair data with the reversed swap (`adjunctionCommutePairDataLeft_of_disjointWindows`), the mirrored
sign/`windowGap` derivation (`disjointWindowsLeft_directedOffset_ge_two`), the reversed-swap COMMUTE builder
(`cellDescentResult_ofCommutePrefixSwapLeft`), and the left-of producer (`commuteCellDescentStepLeft`).  Every
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`.
Auditing the producer transitively covers the private `Nat` helpers. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionContextsFactorDataLeft_of_disjointWindows
#assert_no_axioms FX1Poly.Polygraph.adjunctionCommutePairDataLeft_of_disjointWindows
#assert_no_axioms FX1Poly.Polygraph.disjointWindowsLeft_directedOffset_ge_two
#assert_no_axioms FX1Poly.Polygraph.cellDescentResult_ofCommutePrefixSwapLeft
#assert_no_axioms FX1Poly.Polygraph.commuteCellDescentStepLeft
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyCommuteProducerLeft

end FX1PolyAudit
