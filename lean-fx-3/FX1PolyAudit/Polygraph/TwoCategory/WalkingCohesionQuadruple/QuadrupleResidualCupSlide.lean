import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleResidualCupSlide

/-! # FX1PolyAudit.…WalkingCohesionQuadruple.QuadrupleResidualCupSlide — zero-axiom gate

Per-declaration zero-axiom gate for the residual-cup whisker slide derivation: the two triangle-inverse
solvers, the Godement slide of the two unit cups, the space-side residual cup with its join to the shipped
cross-cup, the residual comultiplication with both insertion mediations, the headline slide theorem, and the
honesty marker.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.quadCodiscUnitUpperWhiskerSolvesToInvCounit
#assert_no_axioms FX1Poly.Polygraph.quadPi0UnitLowerWhiskerSolvesToInvCounit
#assert_no_axioms FX1Poly.Polygraph.quadLowerUnitSlidesPastUpperUnit
#assert_no_axioms FX1Poly.Polygraph.quadSpaceResidualCupViaUpperCell
#assert_no_axioms FX1Poly.Polygraph.quadSpaceResidualCupJoin
#assert_no_axioms FX1Poly.Polygraph.quadResidualComultCell
#assert_no_axioms FX1Poly.Polygraph.quadResidualCupRightInsertion_isComult
#assert_no_axioms FX1Poly.Polygraph.quadResidualCupLeftInsertion_isComult
#assert_no_axioms FX1Poly.Polygraph.quadResidualCupWhiskerSlide
#assert_no_axioms FX1Poly.Polygraph.fxQuadCohesion_hasResidualCupWellPointedEndo

end FX1PolyAudit
