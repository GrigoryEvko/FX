import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReselectionOrbit

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupReselectionOrbit — zero-axiom gate

Per-declaration zero-axiom gate for the cup orbit witness assembled from the leg-aligned re-selection:
`tailsCancel` discharged from the re-selection `AtomicTraceEquiv` via `extractArc_eq_of_atomicTraceEquiv`
at the `codBoundaryLength` seed, with no folded diagram/count legs.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupOrbitWitness_ofReselection
#assert_no_axioms FX1Poly.Polygraph.arcCupOrbitWitness_ofFrontReselection

end FX1PolyAudit
