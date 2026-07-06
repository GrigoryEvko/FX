import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingCupPreservation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPerfectMatchingCupPreservation — zero-axiom gate

Per-declaration zero-axiom gate for the CUP step preservation of the token-frame perfect matching (noFixedPoint
rung, cup half): the forward token map and its four companion lemmas, the two-legs same-component fact, and the
full preservation theorem.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupEndTokenForward_isOldZone
#assert_no_axioms FX1Poly.Polygraph.cupEndTokenBackmap_cupEndTokenForward
#assert_no_axioms FX1Poly.Polygraph.cupEndTokenForward_isValid
#assert_no_axioms FX1Poly.Polygraph.cupEndTokenForward_node
#assert_no_axioms FX1Poly.Polygraph.arcEndTokenNode_below_ofValid
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_legs_sameComponent
#assert_no_axioms FX1Poly.Polygraph.arcPerfectMatchingTokens_stepCupArc

end FX1PolyAudit
