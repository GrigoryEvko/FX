import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDecisionAssembly

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyDecisionAssembly — zero-axiom gate

Per-declaration zero-axiom gate for the #2020 decision assembly from the three colour-keyed sub-producers (Piece I
already discharged): the monolithic residual from the three, the base completeness, the keystone, the full decision,
and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_ofThreeSubProducers
#assert_no_axioms FX1Poly.Polygraph.stringConvOfMapEq_ofThreeSubProducers
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedMatchingCanonicalization_ofThreeSubProducers
#assert_no_axioms FX1Poly.Polygraph.decidableStringSaturatedConv_ofThreeSubProducers
#assert_no_axioms FX1Poly.Polygraph.fxString_hasThreeSubProducerDecisionAssembly

end FX1PolyAudit
