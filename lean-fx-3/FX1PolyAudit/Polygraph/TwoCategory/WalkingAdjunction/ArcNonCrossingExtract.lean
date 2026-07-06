import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingExtract

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcNonCrossingExtract — zero-axiom gate

Per-declaration zero-axiom gate for the extract translation of the non-crossing invariant (cap rung
D2a-iv, extract): the two position renderings coincide, the node readings coincide, token validity,
the forward partner soundness, the partner-in-range bound, the near/far arc endpoints, and the full
`ArcNonCrossing → IsNonCrossing (extractArc …).diagram.partner` translation.  The private clean
Nat-subtraction / map-length / append-read / partner-scan plumbing is covered transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.boundaryPosition_eq_arcEndTokenPosition
#assert_no_axioms FX1Poly.Polygraph.arcEndTokenNode_tokenOfIndex
#assert_no_axioms FX1Poly.Polygraph.isValidArcEndToken_tokenOfIndex
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_sameComponent_or_fixed
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_below
#assert_no_axioms FX1Poly.Polygraph.arcNearFarTokens
#assert_no_axioms FX1Poly.Polygraph.isNonCrossing_extractArc_diagram_partner

end FX1PolyAudit
