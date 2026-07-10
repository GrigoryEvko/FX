import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Graded.GradedAppAnchor

/-! # FX1PolyAudit.Polygraph.Omega.Graded.GradedAppAnchorAudit — zero-axiom gate for the App-rule =
sequential-graded-composite anchor (OMEGA-5 r1, B2).

Per-declaration `#assert_no_axioms` on the forward anchor (the App constructor), the inverse anchor
(via `invertApp`), and the two worked demos (the applied identity and the decisive `r = ω` redex, each
reused through a `gradeCompose`-shaped ascription). -/

namespace FX1PolyAudit

-- GradedAppAnchor.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.appGrade_eq_gradeCompose
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.appGrade_invert_gradeCompose
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.appliedIdentity_typedViaGradeCompose
#assert_no_axioms FX1Poly.Polygraph.Omega.Graded.usageOmegaScalingRedex_typedViaGradeCompose

end FX1PolyAudit
