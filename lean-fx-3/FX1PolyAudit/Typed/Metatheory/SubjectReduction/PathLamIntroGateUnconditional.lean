import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.PathLamIntroGateUnconditional

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.PathLamIntroGateUnconditional — zero-axiom gate

The per-declaration `#assert_no_axioms` gate for the discharge of the `pathLam` intro-gate's last conditional:
`pathLamBodyStepPreservesAppScaledAffine_holds` (typing forces every inner `pathLam` affine, so a stepped body's
App-scaled grade is bounded by `le_trans` against the redex's own affine side condition) and the now-unconditional
seventeenth introducer-congruence row `pathLamIntroGateBranchClosesUnconditional`. -/

namespace FX1PolyAudit

-- ★ The affine-subject-reduction Prop, discharged (composes the typed bridge with beta-stability)
#assert_no_axioms FX1Poly.Typed.pathLamBodyStepPreservesAppScaledAffine_holds

-- ★ The seventeenth intro-gate row, unconditional (no residual hypothesis)
#assert_no_axioms FX1Poly.Typed.pathLamIntroGateBranchClosesUnconditional

end FX1PolyAudit
