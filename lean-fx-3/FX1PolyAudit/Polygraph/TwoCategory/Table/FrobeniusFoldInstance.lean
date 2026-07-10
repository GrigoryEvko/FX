import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusFoldInstance

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.FrobeniusFoldInstance — zero-axiom gate for the deep diagram
invariant's `rowConvInvariant` legs on carrier A (POLY-TAB r1 FROB-RESUME, B2).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`.
The private `inRange_frobLeft_mult` firing witness is covered transitively through `frobeniusSpiderInvariant_vcompLeft_fires`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_rowsPreserve
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_vcompSplit
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_whiskerRightBoundary
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_whiskerLeftBoundary
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_vcompLeftPreserves
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_rowsPreserve_frobLeft
#assert_no_axioms FX1Poly.Polygraph.frobeniusSpiderInvariant_vcompLeft_fires
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasDeepDiagramFoldLegs
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasDeepDiagramFoldInstance

end FX1PolyAudit
