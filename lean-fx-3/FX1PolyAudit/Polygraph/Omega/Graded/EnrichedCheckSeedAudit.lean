import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Graded.EnrichedCheckSeed

/-! # FX1PolyAudit.Polygraph.Omega.Graded.EnrichedCheckSeedAudit — zero-axiom gate for the enriched-
functor seed at the grade-vector level (OMEGA-5 r1, B3).

Per-declaration `#assert_no_axioms` on the usage-factor evaluation, its soundness+completeness, the
usage instance, the functoriality-on-grades legs (monotonicity + the scalar homomorphism), and the
decide-on-a-composite non-vacuity witnesses. -/

namespace FX1PolyAudit

-- EnrichedCheckSeed.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.enrichedCheckOnGrades
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.enrichedCheckOnGrades_correct
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.checkUsageFactor
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeCompose_mono
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeComposePar_mono
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeCompose_scaleHom
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.enrichedCheck_usageAdmits
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.enrichedCheck_usageRejectsOverBudget
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.checkUsageFactor_onSequentialComposite

end FX1PolyAudit
