import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStagedDescent

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStagedDescent — zero-axiom gate (BRAUER-MIDDLE r3, B2)

Per-declaration zero-axiom gate for R3-B: the distant-slide-with-suffix adversarial (genuine move + `straddleCount`
rise), the single-global-lex NO-GO, the OUTER arc-count fuel + its diagram-invariance + per-arc strict descent, and
the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.distantSlideWithSuffix_isMove
#assert_no_axioms FX1Poly.Polygraph.straddleCount_distantSlideWithSuffix_rises
#assert_no_axioms FX1Poly.Polygraph.singleGlobalLexMeasure_refuted
#assert_no_axioms FX1Poly.Polygraph.cupArcCount
#assert_no_axioms FX1Poly.Polygraph.capArcCount
#assert_no_axioms FX1Poly.Polygraph.arcCountFuel
#assert_no_axioms FX1Poly.Polygraph.arcCountFuel_diagram_invariant
#assert_no_axioms FX1Poly.Polygraph.arcCountFuel_strictlyDecreases_perArc
#assert_no_axioms FX1Poly.Polygraph.arcCountFuel_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStagedArcCountFuel
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStagedInnerDescentDischarged

end FX1PolyAudit
