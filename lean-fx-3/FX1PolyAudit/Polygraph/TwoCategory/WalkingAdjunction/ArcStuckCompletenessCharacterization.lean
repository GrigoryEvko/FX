import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStuckCompletenessCharacterization

/-! # FX1PolyAudit/…/ArcStuckCompletenessCharacterization — zero-axiom gate

Per-declaration zero-axiom gate for the general STUCK-case completeness characterization: route (2a)'s uniform
saturation-membership hypothesis proved SUFFICIENT for the unified target `MixedTailArcCompleteness` (the wall:
2a is no shortcut), and the hardest known stuck instance recorded as a (2a) witness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `ofReduceBool`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mixedTailArcCompleteness_of_uniformSaturationMembership
#assert_no_axioms FX1Poly.Polygraph.stuckHardestInstance_isSaturationMember
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcStuckCompletenessCharacterization

end FX1PolyAudit
