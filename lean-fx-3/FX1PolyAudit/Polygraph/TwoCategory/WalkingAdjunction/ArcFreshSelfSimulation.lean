import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshSelfSimulation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcFreshSelfSimulation — zero-axiom gate

Per-declaration zero-axiom gate for the fresh self-simulation: the complement atoms (renaming
closure at-or-above, count vanishing at fresh roots) and the base `ArcStepSimCount` from a
fresh forest state to itself, instantiated at the fresh-block transposition.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.sigmaAtOrAbove_of_fixesBelow
#assert_no_axioms FX1Poly.Polygraph.countEventsInRoot_eq_zero_of_freshRoot
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCount_self_ofFixesBelow
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCount_self_transposition

end FX1PolyAudit
