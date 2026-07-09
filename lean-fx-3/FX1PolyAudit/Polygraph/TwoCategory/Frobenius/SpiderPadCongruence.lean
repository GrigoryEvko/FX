import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderPadCongruence

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.SpiderPadCongruence — zero-axiom gate (WP-FROB r3, FROB-3)

Per-declaration zero-axiom gate for the spider partition pad congruence: the leaner (loops-free) padded
same-component payoff, the relation-in-wider-boundary packaging, the boundary-changing non-vacuity witnesses (the
special law and the Frobenius law fired in strictly wider boundaries), and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- FROB-3: the leaner padded same-component payoff + the relation-in-wider-boundary packaging
#assert_no_axioms FX1Poly.Polygraph.matchingSameComponent_ofSpiderRightPadSimPair
#assert_no_axioms FX1Poly.Polygraph.spiderConv_relation_inWiderBoundary

-- FROB-3: the boundary-changing non-vacuity witnesses
#assert_no_axioms FX1Poly.Polygraph.spiderConv_special_inWiderBoundary
#assert_no_axioms FX1Poly.Polygraph.spiderConv_frobLeft_inWiderBoundary

-- FROB-3: the honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderPadCongruence
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderAfterPrefixContext

end FX1PolyAudit
