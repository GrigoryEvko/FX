import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupRootAtlas

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupRootAtlas — zero-axiom gate

Per-declaration zero-axiom gate for the cup root atlas: the one-cup fresh-triple roots, the
double-cup block roots, old-node locality, the parentless range above, and the old-event count
collapse.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.beq_false_of_lt_left
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_root_leftLeg
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_root_rightLeg
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_root_eventNode
#assert_no_axioms FX1Poly.Polygraph.cupPair_root_firstBlock
#assert_no_axioms FX1Poly.Polygraph.cupPair_root_secondBlock
#assert_no_axioms FX1Poly.Polygraph.cupPair_root_old
#assert_no_axioms FX1Poly.Polygraph.cupPair_root_aboveBlocks
#assert_no_axioms FX1Poly.Polygraph.cupPair_countOldEvents_congr

end FX1PolyAudit
