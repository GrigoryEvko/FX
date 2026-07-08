import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDropLastCup

/-! # FX1PolyAudit/…/MatchingDropLastCup — zero-axiom gate

Per-declaration zero-axiom gate for the plain-carrier top-of-stack cup partner splice and the
width-`0` cup-drop matching-injectivity linchpin (Track B route 1, brick 3): the boundary partner
list of `extractDiagram bc (stepCup S w)` is the base list shifted with the short chord spliced, and
dropping a shared last cup is injective on `matchingOfSpineList 0`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.diagramPartner_stepCup
#assert_no_axioms FX1Poly.Polygraph.dropLastCup_matching_injective
#assert_no_axioms FX1Poly.Polygraph.backAppend_matching_congr

end FX1PolyAudit
