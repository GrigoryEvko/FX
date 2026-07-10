import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundedBoundaryFold

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBoundedBoundaryFold — zero-axiom gate (BRAUER-MIDDLE r10 B2)

Per-declaration zero-axiom gate for the T-DISJOINT fold lift: the alphabet restriction (`isBrauerGenerator`), the
threaded word-predicate (`WellFormedBrauerFold`), the per-atom dispatch
(`boundedBoundaryComponents_stepBrauerAtom`), the structural fold lift
(`boundedBoundaryComponents_processBrauer`), the seed payoff (`boundedBoundaryComponents_reachable`), the
non-vacuity smoke (`wellFormedBrauerFold_capThenCup`), and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the alphabet restriction + the threaded word-predicate
#assert_no_axioms FX1Poly.Polygraph.isBrauerGenerator
#assert_no_axioms FX1Poly.Polygraph.WellFormedBrauerFold

-- the per-atom dispatch + the fold lift + the seed payoff
#assert_no_axioms FX1Poly.Polygraph.boundedBoundaryComponents_stepBrauerAtom
#assert_no_axioms FX1Poly.Polygraph.boundedBoundaryComponents_processBrauer
#assert_no_axioms FX1Poly.Polygraph.boundedBoundaryComponents_reachable

-- non-vacuity smoke
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_capThenCup

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBoundedBoundaryFoldLift
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTagCorrExtraction

end FX1PolyAudit
