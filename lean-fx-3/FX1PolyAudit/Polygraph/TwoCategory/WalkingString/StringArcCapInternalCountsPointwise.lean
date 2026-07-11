import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapInternalCountsPointwise

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapInternalCountsPointwise — zero-axiom gate
(FC-3 r20, THE CLONE CAMPAIGN — Branch A)

Per-declaration zero-axiom gate for the per-port cap-count characterization ported to the adjoint-triple
seed.  The private locked stages (`stringStepPointwiseCap`, `stringPointwiseCapFueled`) are checked
transitively through the public characterizations.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringPureCap_internalCapCounts_pointwise
#assert_no_axioms FX1Poly.Polygraph.stringPureCapSpines_internalCapCountsAgree_ofDiagram
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapInternalCountsPointwise

end FX1PolyAudit
