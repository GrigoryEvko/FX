import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupMixedReselectionReduction

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupMixedReselectionReduction — zero-axiom gate

Per-declaration zero-axiom gate for the unified mixed re-selection target: the completeness of the arc
invariant (`MixedTailArcCompleteness`) named as the single grep-able residual, and the front-head orbit
witness reduction that both shipped pure fronts factor through
(`arcCupOrbitWitness_ofFrontHead_ofCompleteness`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupOrbitWitness_ofFrontHead_ofCompleteness
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupMixedReselectionReduction

end FX1PolyAudit
