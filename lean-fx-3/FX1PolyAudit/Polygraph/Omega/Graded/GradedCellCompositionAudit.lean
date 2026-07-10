import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Graded.GradedCellComposition

/-! # FX1PolyAudit.Polygraph.Omega.Graded.GradedCellCompositionAudit — zero-axiom gate for the cell-side
graded composition (OMEGA-5 r2).

Per-declaration `#assert_no_axioms` on the grade-leg composition laws (associativity + unit), the
reindex counterexample, the enriched-functor grade slice (projections + functor laws +
functor-over-associativity), the refusal slice (guarded composite + collision-row refusal), and the
non-vacuity witnesses on real cells + real kernel grades. -/

namespace FX1PolyAudit

-- GradedCellComposition.lean — B1: the grade-leg algebra of the lockstep composite
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeCompose_assoc
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeCompose_leftUnit
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.usageSingletonZero
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.usageSingletonOne
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.usageSingletonOmega
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeCompose_assoc_corrected_computes
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeCompose_assoc_naive_isFalse

-- GradedCellComposition.lean — B2: the enriched-functor grade slice
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradeOf
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradedVcomp_underlyingCell
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradedVcomp_gradeOf
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradedWhiskerLeft_gradeOf
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradedWhiskerRight_gradeOf
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.gradedVcomp_gradeOf_assoc

end FX1PolyAudit
