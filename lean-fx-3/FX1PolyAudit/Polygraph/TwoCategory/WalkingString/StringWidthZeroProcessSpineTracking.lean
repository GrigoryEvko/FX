import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroProcessSpineTracking

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWidthZeroProcessSpineTracking — zero-axiom
gate (FC-3 r15, B3 locate foundation)

Per-declaration zero-axiom gate for the adjoint-triple-seed open-wire boundary tracking
(`stringProcessSpine_openWires_length_ofChainedAppend` /
`stringProcessSpine_prefix_openWires_eq_lastDomBoundary`) and the marker.  The private `List.range` length
helpers are covered transitively.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_openWires_length_ofChainedAppend
#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_prefix_openWires_eq_lastDomBoundary
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWidthZeroProcessSpineTracking

end FX1PolyAudit
