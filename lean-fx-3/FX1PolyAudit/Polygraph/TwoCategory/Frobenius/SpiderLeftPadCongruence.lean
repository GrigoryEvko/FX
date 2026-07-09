import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderLeftPadCongruence

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.SpiderLeftPadCongruence — zero-axiom gate (WP-FROB r6, FROB-6)

Per-declaration zero-axiom gate for the spider partition pad congruence at a nonzero LEFT offset (boundary-changing):
the leaner (loops-free) left-padded same-component payoff, the relation-at-left-offset packaging, the
boundary-changing + nonzero-offset non-vacuity witnesses (the special law and the Frobenius law fired at a shifted
left offset), the partition-real witness, and the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- FROB-6: the leaner left-padded same-component payoff + the relation-at-left-offset packaging
#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent_ofSpiderLeftPadSimPair
#assert_no_axioms FX1Poly.Polygraph.spiderConv_relation_inWiderBoundary_leftOffset

-- FROB-6: the boundary-changing + nonzero-offset non-vacuity witnesses
#assert_no_axioms FX1Poly.Polygraph.spiderConv_special_atLeftOffset
#assert_no_axioms FX1Poly.Polygraph.spiderConv_frobLeft_atLeftOffset
#assert_no_axioms FX1Poly.Polygraph.spiderConv_special_atLeftOffset_identifies_distinct
#assert_no_axioms FX1Poly.Polygraph.spiderConv_special_atLeftOffset_partitionAgrees

-- FROB-6: the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderBoundaryChangingPadLeft

end FX1PolyAudit
