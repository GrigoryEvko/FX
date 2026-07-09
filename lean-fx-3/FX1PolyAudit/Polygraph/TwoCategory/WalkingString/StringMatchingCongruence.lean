import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingCongruence

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the saturated-congruence discharge: the universal cup/cap discipline over the
walking adjoint triple, the three `{signature}`-generic vcomp boundary-dispatch congruences, the two whisker
congruences at the string signature, the four-field `StringMatchingSaturatedCongruence` bundle inhabitant, and
the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cellHasCupCapGenerators_ofStringSignature
#assert_no_axioms FX1Poly.Polygraph.matchingOf_vcompLeft_congr_ofDiscipline
#assert_no_axioms FX1Poly.Polygraph.matchingOf_vcompRight_congr_ofMidBoundaryPos_ofDiscipline
#assert_no_axioms FX1Poly.Polygraph.matchingOf_vcompRight_congr_ofDiscipline
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOf_whiskerLeft_congruence
#assert_no_axioms FX1Poly.Polygraph.stringMatchingOf_whiskerRight_congruence
#assert_no_axioms FX1Poly.Polygraph.stringMatchingSaturatedCongruence_proved
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMatchingSaturatedCongruence

end FX1PolyAudit
