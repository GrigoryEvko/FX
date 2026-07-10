import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.InvariantFoldInstances

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.InvariantFoldInstances — zero-axiom gate for the REAL
invariant-fold instances (POLY-TAB r1, P1).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.frobeniusBoundaryLength
#assert_no_axioms FX1Poly.Polygraph.frobeniusBoundaryLength_fold
#assert_no_axioms FX1Poly.Polygraph.frobeniusBoundaryLength_frobLeft_fires
#assert_no_axioms FX1Poly.Polygraph.frobeniusBoundaryLength_unitLeft_fires
#assert_no_axioms FX1Poly.Polygraph.FrobeniusBoundary
#assert_no_axioms FX1Poly.Polygraph.frobeniusBoundaryOf
#assert_no_axioms FX1Poly.Polygraph.frobeniusBoundaryOf_fold
#assert_no_axioms FX1Poly.Polygraph.frobeniusBoundaryOf_frobLeft_fires
#assert_no_axioms FX1Poly.Polygraph.frobeniusSameBoundaryLength
#assert_no_axioms FX1Poly.Polygraph.frobeniusSameBoundaryLength_isCongruence
#assert_no_axioms FX1Poly.Polygraph.frobeniusSameBoundaryLength_foldRel
#assert_no_axioms FX1Poly.Polygraph.frobeniusSameBoundaryLength_frobLeft_fires
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasRealInvariantFoldInstances

end FX1PolyAudit
