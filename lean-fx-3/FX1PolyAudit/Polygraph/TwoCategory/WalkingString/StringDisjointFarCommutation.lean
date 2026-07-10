import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointFarCommutation

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringDisjointFarCommutation — zero-axiom gate (FC-3 r1, B3)

Per-declaration zero-axiom gate for the disjoint-boundary far-commutation: the disjoint-whisker exchange at the
saturated relation (both directions), the real-generator non-vacuity witness, and the residual-localization marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringDisjointWhiskerExchange
#assert_no_axioms FX1Poly.Polygraph.stringDisjointWhiskerExchange_symm
#assert_no_axioms FX1Poly.Polygraph.stringDisjointFarCommutation_onUnitLower
#assert_no_axioms FX1Poly.Polygraph.fxString_hasDisjointFarCommutation

end FX1PolyAudit
