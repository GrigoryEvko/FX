import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringJointInvariant

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringJointInvariant — zero-axiom gate (STRING-JOINT r1)

Per-declaration zero-axiom gate for the JOINT reachable-class invariant + the label-read `capPin` projection: the
non-crossing arity wrapper, the bundled invariant seed / step / fold / seed-capstone, the pure `pathLabels ∘
composePath` reads, the cap-generator dom-word fact, and the assembled cap-window non-cup-word projection.  Must be
free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.StringNonCrossing_stepAtom
#assert_no_axioms FX1Poly.Polygraph.stringJointInvariant_initial
#assert_no_axioms FX1Poly.Polygraph.stringJointInvariant_stepAtom
#assert_no_axioms FX1Poly.Polygraph.stringJointInvariant_processSpine_ofChained
#assert_no_axioms FX1Poly.Polygraph.stringJointInvariant_fromCell
#assert_no_axioms FX1Poly.Polygraph.stringPathLabels_read_pastLeft
#assert_no_axioms FX1Poly.Polygraph.stringPathLabels_read_belowLeft
#assert_no_axioms FX1Poly.Polygraph.stringCapGeneratorDomWord_notCupWord
#assert_no_axioms FX1Poly.Polygraph.stringCapWindow_notCupWord

end FX1PolyAudit
