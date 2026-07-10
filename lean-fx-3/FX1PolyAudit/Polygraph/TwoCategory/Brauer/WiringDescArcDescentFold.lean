import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcDescentFold

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcDescentFold — zero-axiom gate (BRAUER-ARC-DESCENT r1, B2)

Per-declaration zero-axiom gate for the Σ-carried arc-sink fold mechanism: the three sink rungs (cup-past-cap /
cup-past-crossing / cup-past-cup, each extending a `BrauerConvFree8` accumulator with a strict `arcMeasure` drop),
the two-rung fold demo, and the two honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcSink_cupCap
#assert_no_axioms FX1Poly.Polygraph.arcSink_cupCrossing
#assert_no_axioms FX1Poly.Polygraph.arcSink_cupCup
#assert_no_axioms FX1Poly.Polygraph.arcSinkFold_demo
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasArcDescentSinkMechanism
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasArcDescentFold

end FX1PolyAudit
