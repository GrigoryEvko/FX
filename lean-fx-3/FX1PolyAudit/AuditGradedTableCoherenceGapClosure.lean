import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.GradedTableCoherenceGapClosure

/-! # FX1PolyAudit/AuditGradedTableCoherenceGapClosure — the two pinned directional gaps, closed

Per-declaration zero-axiom gate for the closure of the two directional residuals pinned in
`FX1Poly/Typed/GradedTableCoherence.lean` (the keystone iff `gradedBinderChecks_iff_gradeSubsumption`'s
forward and backward directions):

  * the BACKWARD residual, CLOSED as the strengthened admissible-grade iff
    (`identityGradeableIffBinderGradeOne`), the exact-image closure
    (`tableCheckAtExactImage_derivesIdentity`, with `identityCountImageIsOne`), and the strict-slack
    tightness pin (`backwardResidualIsStrictSlack`);
  * the FORWARD residual, PROVEN TIGHT via the keystone iff
    (`affineDuplicatorViolatesGradeSubsumption` / `forwardGapIsGenuine` — the judgment grade sits
    strictly below the body's count image);
  * the combined verdict record and its witness
    (`GradedTableCoherenceGapClosureVerdict` / `gradedTableCoherenceGapClosureVerdict`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The backward gap, CLOSED as a strengthened iff -/

#assert_no_axioms FX1Poly.Typed.identityGradeableIffBinderGradeOne
#assert_no_axioms FX1Poly.Typed.identityCountImageIsOne
#assert_no_axioms FX1Poly.Typed.tableCheckAtExactImage_derivesIdentity
#assert_no_axioms FX1Poly.Typed.backwardResidualIsStrictSlack

/-! ## The forward gap, PROVEN TIGHT via the keystone iff -/

#assert_no_axioms FX1Poly.Typed.affineDuplicatorViolatesGradeSubsumption
#assert_no_axioms FX1Poly.Typed.forwardGapIsGenuine

/-! ## The combined gap-closure verdict record + witness -/

#assert_no_axioms FX1Poly.Typed.GradedTableCoherenceGapClosureVerdict
#assert_no_axioms FX1Poly.Typed.gradedTableCoherenceGapClosureVerdict

end FX1PolyAudit
