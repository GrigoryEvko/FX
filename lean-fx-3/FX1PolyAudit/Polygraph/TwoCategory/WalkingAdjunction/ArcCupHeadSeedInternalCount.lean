import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadSeedInternalCount

/-! # FX1PolyAudit/…/ArcCupHeadSeedInternalCount — zero-axiom gate

Per-declaration zero-axiom gate for the head cup's `internalCupCounts` contribution (R1a): on the fresh seed
a single cup at window `windowPosition ≤ bottomCount` contributes EXACTLY one cup event to its two leg ports'
strand — node-level, port-indexed, and on the `FullArcStructure.internalCupCounts` field.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupHeadSeed_cupEventCount_leftLeg
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadSeed_cupEventCount_rightLeg
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadSeed_internalCupCountAt_leftLegPort
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadSeed_internalCupCountAt_rightLegPort
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadSeed_internalCupCounts_leftLegField
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadSeed_internalCupCounts_rightLegField
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupHeadSeedInternalCount

end FX1PolyAudit
