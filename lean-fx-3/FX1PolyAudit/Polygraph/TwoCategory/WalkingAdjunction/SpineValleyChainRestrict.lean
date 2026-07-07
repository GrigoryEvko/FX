import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyChainRestrict

/-! # FX1PolyAudit/…/SpineValleyChainRestrict — zero-axiom gate

Per-declaration zero-axiom gate for the Piece-I cup-suffix chain restriction: restricting a whole-valley
boundary chain to the cup suffix over a pure-cap prefix.  Every declaration must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_cupSuffix_ofCapPrefix
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyChainRestrict

end FX1PolyAudit
