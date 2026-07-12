import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringTwoSubProducerBeam

/-! # FX1PolyAudit/…/WalkingString/StringTwoSubProducerBeam — zero-axiom gate
(FC-3 r38, the beam re-wired from three colour-keyed sub-producers to two)

Per-declaration zero-axiom gate for the two-sub-producer beam re-wiring over the walking ADJOINT-TRIPLE signature:
the beam `stringMatchingReductsShareSpineTrace_ofTwoSubProducers`, the base completeness
`stringConvOfMapEq_ofTwoSubProducers`, the full decision `decidableStringSaturatedConv_ofTwoSubProducers`, and the
honesty marker.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` lines
below are the trusted cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_ofTwoSubProducers
#assert_no_axioms FX1Poly.Polygraph.stringConvOfMapEq_ofTwoSubProducers
#assert_no_axioms FX1Poly.Polygraph.decidableStringSaturatedConv_ofTwoSubProducers
#assert_no_axioms FX1Poly.Polygraph.fxString_hasTwoSubProducerBeam

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_ofTwoSubProducers
#print axioms FX1Poly.Polygraph.stringConvOfMapEq_ofTwoSubProducers
#print axioms FX1Poly.Polygraph.decidableStringSaturatedConv_ofTwoSubProducers
#print axioms FX1Poly.Polygraph.fxString_hasTwoSubProducerBeam

end FX1PolyAudit
