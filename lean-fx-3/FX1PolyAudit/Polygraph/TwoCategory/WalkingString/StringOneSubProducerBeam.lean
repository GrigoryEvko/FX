import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringOneSubProducerBeam

/-! # FX1PolyAudit/…/WalkingString/StringOneSubProducerBeam — zero-axiom gate
(FC-3 r39, the beam re-wired from two colour-keyed sub-producers to one)

Per-declaration zero-axiom gate for the one-sub-producer beam re-wiring over the walking ADJOINT-TRIPLE signature:
the beam `stringMatchingReductsShareSpineTrace_ofOneSubProducer`, the base completeness
`stringConvOfMapEq_ofOneSubProducer`, the full decision `decidableStringSaturatedConv_ofOneSubProducer`, and the
honesty marker.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` lines
below are the trusted cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_ofOneSubProducer
#assert_no_axioms FX1Poly.Polygraph.stringConvOfMapEq_ofOneSubProducer
#assert_no_axioms FX1Poly.Polygraph.decidableStringSaturatedConv_ofOneSubProducer
#assert_no_axioms FX1Poly.Polygraph.fxString_hasOneSubProducerBeam

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_ofOneSubProducer
#print axioms FX1Poly.Polygraph.stringConvOfMapEq_ofOneSubProducer
#print axioms FX1Poly.Polygraph.decidableStringSaturatedConv_ofOneSubProducer
#print axioms FX1Poly.Polygraph.fxString_hasOneSubProducerBeam

end FX1PolyAudit
