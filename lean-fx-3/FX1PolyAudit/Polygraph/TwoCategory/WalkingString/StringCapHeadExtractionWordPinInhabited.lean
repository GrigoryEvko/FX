import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapHeadExtractionWordPinInhabited

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringCapHeadExtractionWordPinInhabited — zero-axiom gate
(FC-3 r26)

Per-declaration zero-axiom gate for the pin-prime inhabitant assembly.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the
independent `#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

-- G-a — the AllCapArity prefix-of-append inversion
#assert_no_axioms FX1Poly.Polygraph.stringAllCapArity_prefix_ofAppend

-- truth-probes
#assert_no_axioms FX1Poly.Polygraph.stringInhabitSeatProbe
#assert_no_axioms FX1Poly.Polygraph.stringInhabitPrefixInversionProbe
#assert_no_axioms FX1Poly.Polygraph.stringInhabitBoundaryProbe

-- ★★ the pin-prime inhabitant (transitively covers all private helpers: order-preservation, seat, conjuncts)
#assert_no_axioms FX1Poly.Polygraph.stringCapHeadExtractionWordPinInhabited

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringAllCapArity_prefix_ofAppend
#print axioms FX1Poly.Polygraph.stringInhabitSeatProbe
#print axioms FX1Poly.Polygraph.stringInhabitPrefixInversionProbe
#print axioms FX1Poly.Polygraph.stringInhabitBoundaryProbe
#print axioms FX1Poly.Polygraph.stringCapHeadExtractionWordPinInhabited

end FX1PolyAudit
