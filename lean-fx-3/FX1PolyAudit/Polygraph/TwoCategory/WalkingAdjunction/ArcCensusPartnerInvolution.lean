import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerInvolution

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCensusPartnerInvolution — zero-axiom gate

Per-declaration zero-axiom gate for the censused partner-matching involution (short-chord prereq): at a
censused state the genuine partner of a genuine partner is the original index.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_isInvolution

end FX1PolyAudit
