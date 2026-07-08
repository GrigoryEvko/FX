import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingStepCupWindowPartner

/-! # FX1PolyAudit/…/MatchingStepCupWindowPartner — zero-axiom gate

Per-declaration zero-axiom gate for the two census-free plain-carrier window partners (Track B
route 1, brick 3): a folded cup's two fresh legs partner each other on the plain matching carrier,
pinned by the direct freshness argument (no census involution).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_ofFreshLegPair
#assert_no_axioms FX1Poly.Polygraph.generalStateCupForwardPartnerMatching
#assert_no_axioms FX1Poly.Polygraph.generalStateCupBackwardPartnerMatching

end FX1PolyAudit
