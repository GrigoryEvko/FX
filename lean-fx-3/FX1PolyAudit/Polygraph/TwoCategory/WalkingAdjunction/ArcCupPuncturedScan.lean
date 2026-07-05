import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupPuncturedScan

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupPuncturedScan — zero-axiom gate

Per-declaration zero-axiom gate for the punctured-scan OFF leg (peel campaign H, cup
rung 2c): the off-component join invisibility and the off-fused partner correspondence —
away from the peeled cup's fused strand, the cup is transparent to the partner structure.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_offComponent
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_partnerScan_offFused

end FX1PolyAudit
