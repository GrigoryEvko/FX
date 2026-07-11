import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapBoundaryReads

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapBoundaryReads — zero-axiom gate
(FC-3 r20, THE CLONE CAMPAIGN — floor)

Per-declaration zero-axiom gate for the cap-head composite boundary reads ported to the adjoint-triple seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_boundaryRead_belowWindow
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_boundaryRead_atOrPastWindow
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_totalPorts
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapBoundaryReads

end FX1PolyAudit
