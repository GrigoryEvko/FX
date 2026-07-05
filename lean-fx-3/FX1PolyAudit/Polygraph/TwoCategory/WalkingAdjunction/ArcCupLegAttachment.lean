import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLegAttachment

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupLegAttachment — zero-axiom gate

Per-declaration zero-axiom gate for the leg-attachment separation kit (peel campaign H, cup
rung 4 opener): the bottom-port read, the census-powered leg separation from a fused witness
on either leg, and the leg-exclusion corollaries.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListGetAt_rangeAppend_below
#assert_no_axioms FX1Poly.Polygraph.arcFreshLegsDisconnected_ofFusedWitness
#assert_no_axioms FX1Poly.Polygraph.arcFreshLegsDisconnected_ofFusedWitnessRight
#assert_no_axioms FX1Poly.Polygraph.arcLegReach_neOppositeLeg
#assert_no_axioms FX1Poly.Polygraph.arcLegReach_neRightLeg

end FX1PolyAudit
