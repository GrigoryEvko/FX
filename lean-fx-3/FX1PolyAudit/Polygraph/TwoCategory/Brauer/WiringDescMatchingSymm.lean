import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescMatchingSymm

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescMatchingSymm — zero-axiom gate (BRAUER r29 B1)

Per-declaration zero-axiom gate for the two r29 dispatch EXPOSURES: the public boundary-matching symmetry
(`matchingSameComponent_symm` + its `= true` reorientation `matchingSameComponent_flipTrue`) and the public
value→rank roundtrip (`natIndexOfValueRoundtrip`).  Both are one-line promotions of lane-private copies, carrying no
new axiom dependency.

Independent `#print axioms` (in a scratch during development) reported every decl as "does not depend on any axioms".
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- the two exposures
#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent_symm
#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent_flipTrue
#assert_no_axioms FX1Poly.Polygraph.natIndexOfValueRoundtrip

-- B1: the classification truth-probes
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_mixedProbe
#assert_no_axioms FX1Poly.Polygraph.classificationProbe_bottom_mixed
#assert_no_axioms FX1Poly.Polygraph.classificationProbe_top_mixed
#assert_no_axioms FX1Poly.Polygraph.classificationProbe_allThrough
#assert_no_axioms FX1Poly.Polygraph.classificationProbe_allLoop

end FX1PolyAudit
