import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingKZ.KZMonadPresentation

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingKZ.KZMonadPresentation — zero-axiom gate (the walking-KZ presentation)

Per-declaration zero-axiom gate for the walking Kock-Zoberlein monad presentation: the two comparison-endpoint
faces, the directed 2-cell PREORDER `KZTwoCellLE`, KZ equality, and the presentation witnesses.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.kzTEtaCell
#assert_no_axioms FX1Poly.Polygraph.kzEtaTCell
#assert_no_axioms FX1Poly.Polygraph.KZTwoCellLE
#assert_no_axioms FX1Poly.Polygraph.KZTwoCellEq
#assert_no_axioms FX1Poly.Polygraph.kzComparisonHolds
#assert_no_axioms FX1Poly.Polygraph.KZTwoCellLE.ofMonadLaw
#assert_no_axioms FX1Poly.Polygraph.kzComparisonWhiskeredHolds
#assert_no_axioms FX1Poly.Polygraph.kzLeftUnitEq
#assert_no_axioms FX1Poly.Polygraph.kzComparisonViaTrans
#assert_no_axioms FX1Poly.Polygraph.fxKZ_hasWalkingKZPresentation

end FX1PolyAudit
