import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSingleWindowReadoff

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupSingleWindowReadoff — zero-axiom gate

Per-declaration zero-axiom gate for the single-cup forward-partner readoff (rung 1 of the cup window inversion):
the lone cup on the fresh seed sends `partnerIndexOf` to the right leg, forced by the two nested `unionFindJoin`s.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.singleCupForwardPartner
#assert_no_axioms FX1Poly.Polygraph.singleCupReversePartner

end FX1PolyAudit
