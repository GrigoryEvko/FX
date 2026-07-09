import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingCompleteness

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingCompleteness — zero-axiom gate

Per-declaration zero-axiom gate for the r3 completeness ingredients: the free-trace lift into the saturated string
relation, the completeness reduction (base + two-level) from the named reduct-existence residual, the keystone and
the gated decision, the two unconditional non-vacuity poles (the convertible `G`-snakes, the non-convertible unit
faces), and the three markers (the shipped-lift marker, the NO-coherence-gap wall record, and the still-open
completeness marker).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.StringSaturatedTwoCellConv.ofSpineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.StringMatchingReductsShareSpineTrace
#assert_no_axioms FX1Poly.Polygraph.stringConvOfMapEq_ofReductsShareSpineTrace
#assert_no_axioms FX1Poly.Polygraph.stringConvOfColouredMapEq_ofReductsShareSpineTrace
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedMatchingCanonicalization_ofReducts
#assert_no_axioms FX1Poly.Polygraph.decidableStringSaturatedConv_ofReducts
#assert_no_axioms FX1Poly.Polygraph.decideStringSaturated_gSnakes_convertible
#assert_no_axioms FX1Poly.Polygraph.stringUnitFaceLeft
#assert_no_axioms FX1Poly.Polygraph.stringUnitFaceRight
#assert_no_axioms FX1Poly.Polygraph.stringUnitFaces_colouredMatchingOf_ne
#assert_no_axioms FX1Poly.Polygraph.stringUnitFaces_notSaturatedConv
#assert_no_axioms FX1Poly.Polygraph.fxString_hasSpineTraceLiftIntoStringSaturated
#assert_no_axioms FX1Poly.Polygraph.fxString_hasAdjointTripleCoherenceGap
#assert_no_axioms FX1Poly.Polygraph.fxString_hasAdjointTripleCompleteness

end FX1PolyAudit
