import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundedBoundaryComponents

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBoundedBoundaryComponents — zero-axiom gate
(BRAUER-MIDDLE r6, B1 partial: the T-DISJOINT invariant, its seed, and non-vacuity)

Per-declaration zero-axiom gate for the forest-cardinality invariant `boundedBoundaryComponents`, its arbitrary-
`bottomCount` seed base case `boundedBoundaryComponents_seed`, the refutation `boundedBoundaryComponents_notMonochromatic`,
the decidable bounded proxy `boundedBoundaryComponentsCheck` with its mixed-diagram firings, and the two honesty
markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.boundedBoundaryComponents
#assert_no_axioms FX1Poly.Polygraph.boundedBoundaryComponents_seed
#assert_no_axioms FX1Poly.Polygraph.overConnectedProbeState
#assert_no_axioms FX1Poly.Polygraph.boundedBoundaryComponents_notMonochromatic
#assert_no_axioms FX1Poly.Polygraph.sameComponentTripleFree
#assert_no_axioms FX1Poly.Polygraph.boundedBoundaryComponentsCheck
#assert_no_axioms FX1Poly.Polygraph.boundedBoundaryComponentsCheck_crossing
#assert_no_axioms FX1Poly.Polygraph.boundedBoundaryComponentsCheck_capThenCup
#assert_no_axioms FX1Poly.Polygraph.boundedBoundaryComponents_stepCap
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBoundedBoundaryComponentsSeed
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTagCorrDisjoint

end FX1PolyAudit
