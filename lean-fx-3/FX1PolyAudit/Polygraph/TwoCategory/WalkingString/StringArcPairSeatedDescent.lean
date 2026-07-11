import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcPairSeatedDescent

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcPairSeatedDescent — zero-axiom gate
(FC-3 r22, B2 P2)

Per-declaration zero-axiom gate for the cap-step gap-closing exclusion at the adjoint triple and its marker.  Must
be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcPairSeated_beforeCapStep_ofTipParities
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcPairSeatedDescent

end FX1PolyAudit
