import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Graded.GradedCell

/-! # FX1PolyAudit.Polygraph.Omega.Graded.GradedCellAudit — zero-axiom gate for the graded cell + the
composition arithmetic (OMEGA-5 r1, B1).

Per-declaration `#assert_no_axioms` on the extrinsic-product carrier, its projections, the sequential /
parallel grade composites, the graded vcomp / whiskers, and the computing non-vacuity witnesses. -/

namespace FX1PolyAudit

-- GradedCell.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.GradedCell
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.GradedCell.underlyingCell
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.GradedCell.gradeVector
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeCompose
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeComposePar
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradedVcomp
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradedWhiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradedWhiskerRight
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeCompose_usageIdentity_computes
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeCompose_usageOmega_computes
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeComposePar_usageLinearSplit_computes
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.demoComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.demoCellThree
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.demoGradedCellThree
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.demoGradedVcomp_cellComputes
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.demoGradedVcomp_gradeComputes

end FX1PolyAudit
