import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingCapPreservation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPerfectMatchingCapPreservation — zero-axiom gate

Per-declaration zero-axiom gate for the CAP step preservation of the token-frame perfect matching (noFixedPoint
rung, cap half): the survivor forward token map and its companion lemmas, the two-removed-wires
same-component fact, and the full census-coupled preservation theorem.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capEndTokenBackmap_capEndTokenForward
#assert_no_axioms FX1Poly.Polygraph.capEndTokenForward_isValid
#assert_no_axioms FX1Poly.Polygraph.capEndTokenForward_node
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_wires_sameComponent
#assert_no_axioms FX1Poly.Polygraph.arcPerfectMatchingTokens_stepCapArc

end FX1PolyAudit
