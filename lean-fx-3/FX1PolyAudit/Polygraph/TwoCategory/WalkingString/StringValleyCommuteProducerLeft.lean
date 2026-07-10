import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCommuteProducerLeft

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyCommuteProducerLeft — zero-axiom gate (FC-3 r6, B2)

Per-declaration zero-axiom gate for the LEFT-of string COMMUTE producer: the mirrored pair-data bundle and its
builder, the mirrored directed-offset bound, the producer, and the honesty marker.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.StringCommutePairDataLeft
#assert_no_axioms FX1Poly.Polygraph.stringCommutePairDataLeft_of_disjointWordWindows
#assert_no_axioms FX1Poly.Polygraph.stringDisjointWindowsLeft_directedOffset_ge_two
#assert_no_axioms FX1Poly.Polygraph.stringCommuteCellDescentStepLeft
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringValleyCommuteProducerLeft

end FX1PolyAudit
