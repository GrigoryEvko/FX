import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCountLegJoinedAgreement

/-! # FX1PolyAudit/…/ArcCupCountLegJoinedAgreement — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head internal-count leg-joined agreement: under the
same-classification precondition the two runs' leg-joined censuses coincide (the head contribution
cancels), isolating the internal-count residual as the leg-attachment de-merge.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupCountTransport_baseAgrees_ofSameClassification
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupCountLegJoinedAgreement

end FX1PolyAudit
