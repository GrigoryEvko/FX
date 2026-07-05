import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPairLocateTouch

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPairLocateTouch — zero-axiom gate

Per-declaration zero-axiom gate for the head-location scan: the touch predicate, the split
certificate, its lift over a leading atom, the scan induction (untouched survival or a
pair-touching cap split), and the unconditional split under the final partner pin.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ArcReadsTouchPair
#assert_no_axioms FX1Poly.Polygraph.ArcPairTouchSplit
#assert_no_axioms FX1Poly.Polygraph.arcPairTouchSplit_ofSteppedTail
#assert_no_axioms FX1Poly.Polygraph.arcPairUntouched_locateTouch
#assert_no_axioms FX1Poly.Polygraph.arcPairTouchSplit_ofPartnerPin
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPairTouchLocation

end FX1PolyAudit
