import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringStraightenOracleWireUp

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringStraightenOracleWireUp — zero-axiom gate (FC-3 r7, B4)

Per-declaration zero-axiom gate for the descent-oracle verdict dispatch: the RIGHT-straighten producer type and the
located-pair dispatch.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.StringRightStraightenProducer
#assert_no_axioms FX1Poly.Polygraph.stringDescentDispatch_ofLocatedPair
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringDescentDispatchModuloRightMirror

end FX1PolyAudit
