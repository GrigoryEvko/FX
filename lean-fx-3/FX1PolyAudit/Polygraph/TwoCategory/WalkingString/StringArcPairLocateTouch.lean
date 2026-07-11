import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcPairLocateTouch

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcPairLocateTouch — zero-axiom gate
(FC-3 r19, THE CAP-HEAD DISCHARGE PORT — LOCATE floor)

Per-declaration zero-axiom gate for the head-location scan ported to the adjoint-triple seed: the split certificate,
its lift over a leading atom, the scan induction (untouched survival or a pair-touching cap split), and the
unconditional split under the final partner pin.  (`ArcReadsTouchPair` is the reused generic touch predicate, already
gated by the arc twin.)

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.StringArcPairTouchSplit
#assert_no_axioms FX1Poly.Polygraph.stringArcPairTouchSplit_ofSteppedTail
#assert_no_axioms FX1Poly.Polygraph.stringArcPairUntouched_locateTouch
#assert_no_axioms FX1Poly.Polygraph.stringArcPairTouchSplit_ofPartnerPin
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcPairTouchLocation

end FX1PolyAudit
