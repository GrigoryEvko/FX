import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyTopCountTotal

/-! # FX1PolyAudit/…/ValleyTopCountTotal — zero-axiom gate

Per-declaration zero-axiom gate for the cap `topCount` field of the full `capRestrict` `DiagramType.ext`
(Piece II tail): the abstract full-image count identity and the concrete survivor-top-total = mid-width.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.countBelow_atStrictMonoImage_full_eq_sourceLength
#assert_no_axioms FX1Poly.Polygraph.survivorTopTotal_eq_midWidth
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasValleyTopCountTotal

end FX1PolyAudit
