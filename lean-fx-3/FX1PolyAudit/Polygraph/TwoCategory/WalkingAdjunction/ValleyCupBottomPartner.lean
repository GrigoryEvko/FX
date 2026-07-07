import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupBottomPartner

/-! # FX1PolyAudit/…/ValleyCupBottomPartner — zero-axiom gate

Per-declaration zero-axiom gate for the cup-BOTTOM and cup-TOP-survivor partner fields of `cupRestrict` (Piece II
tail): the cup-alone bottom partner and the two partner-field agreements that ride the seed-agnostic concrete cup
embedding (the cup duals of the cap survivor-bottom / cap-TOP cases).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupAlone_survivorPartner
#assert_no_axioms FX1Poly.Polygraph.cupRestrict_partner_cupBottom
#assert_no_axioms FX1Poly.Polygraph.cupRestrict_partner_survivorTop
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCupBottomAndSurvivorTopPartner

end FX1PolyAudit
