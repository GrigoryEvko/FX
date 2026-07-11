import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupBottomPartner

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyCupBottomPartner — zero-axiom gate
(FC-3 r33, B5: the cup-BOTTOM and cup-TOP-survivor partner fields of `cupRestrict`)

Per-declaration zero-axiom gate for the string cup-side partner legs over the walking ADJOINT-TRIPLE signature: the
cup-alone bottom partner, the cup-bottom partner agreement, the cup-top survivor-top partner agreement, and the two
truth-probe firings on the wide (mid-width `2`) valley.  The private range/`Nat.blt` plumbing (`rangeLoopLenSCBP`,
…, `bltTrueOfLtSCBP`) and the private `stringValleyRootsFloorSeparated` are covered transitively.  Every declaration
must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The project
`#assert_no_axioms` macro is fuel-based; the independent `#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCupAlone_survivorPartner
#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_partner_cupBottom
#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_partner_survivorTop
#assert_no_axioms FX1Poly.Polygraph.stringCupRestrict_partner_cupBottom_firesOnWideValley
#assert_no_axioms FX1Poly.Polygraph.stringCupAlone_survivorPartner_firesOnWideCupBlock
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCupBottomAndSurvivorTopPartner

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringCupAlone_survivorPartner
#print axioms FX1Poly.Polygraph.stringCupRestrict_partner_cupBottom
#print axioms FX1Poly.Polygraph.stringCupRestrict_partner_survivorTop
#print axioms FX1Poly.Polygraph.stringCupRestrict_partner_cupBottom_firesOnWideValley
#print axioms FX1Poly.Polygraph.stringCupAlone_survivorPartner_firesOnWideCupBlock
#print axioms FX1Poly.Polygraph.fxString_hasCupBottomAndSurvivorTopPartner

end FX1PolyAudit
