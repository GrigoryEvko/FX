import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapPartnerList

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapPartnerList — zero-axiom gate

Per-declaration zero-axiom gate for the assembled composite partner list (peel campaign H,
rung E-3, part 6): the composite extract's whole partner list is the fresh partner list
transported by the two-zone index shift with the consumed window pair spliced in at the
window position.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_partnerListCorr

end FX1PolyAudit
