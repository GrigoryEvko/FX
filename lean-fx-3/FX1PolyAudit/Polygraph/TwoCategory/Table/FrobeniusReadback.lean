import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusReadback

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.FrobeniusReadback — zero-axiom gate for the A->B readback +
the deep diagram invariant on carrier A (POLY-TAB r1 FROB-RESUME, B1).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.frobeniusReadbackGen
#assert_no_axioms FX1Poly.Polygraph.readbackToWord
#assert_no_axioms FX1Poly.Polygraph.readbackToWord_vcomp
#assert_no_axioms FX1Poly.Polygraph.readbackToWord_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.readbackToWord_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.readbackToWord_castBoundary
#assert_no_axioms FX1Poly.Polygraph.readbackToWord_unitLeftCell
#assert_no_axioms FX1Poly.Polygraph.readbackToWord_idTCell
#assert_no_axioms FX1Poly.Polygraph.readbackToWord_leftLhsCell
#assert_no_axioms FX1Poly.Polygraph.readbackToWord_HCell
#assert_no_axioms FX1Poly.Polygraph.readbackToWord_rightLhsCell
#assert_no_axioms FX1Poly.Polygraph.readbackToWord_specialCell
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_unitLeft
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_frobLeft
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_frobRight
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_special
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_frobLeft_realizes
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_twoValues
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_H_ne_identityPair
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasFrobeniusReadbackInvariant

end FX1PolyAudit
