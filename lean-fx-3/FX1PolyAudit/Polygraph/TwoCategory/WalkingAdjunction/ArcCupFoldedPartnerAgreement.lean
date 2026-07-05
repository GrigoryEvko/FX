import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedPartnerAgreement

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupFoldedPartnerAgreement — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head partner cancel's same-classification assembly: the
per-index fresh partner agreement from the two shipped same-classification cells (both-off, both-fused),
consuming a same-classification precondition that excludes the mixed cell (the through-the-head orbit's
target).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupFoldedPartner_agrees_ofSameClassification
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupFoldedPartnerAgreement

end FX1PolyAudit
