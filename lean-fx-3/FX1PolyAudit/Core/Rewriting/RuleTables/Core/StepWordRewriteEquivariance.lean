import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Core.StepWordRewriteEquivariance

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Core.StepWordRewriteEquivariance

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Core.StepWordRewriteEquivariance`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Rename/subst-equivariance of the Step-to-word bridge + system-level inversion.  The soundness commutes
-- with the term rename/subst actions (Step.toWordRewrite_rename/_subst, StepStar.toWordRewrites_rename, via
-- Step.rename/Step.subst/StepStar.rename) and the generated system is closed under both
-- (fxStepSystem_rename_mem/_subst_mem).  fxStepSystem_imp_step inverts the system (every rule comes from a
-- Step) + _leftHandSide/_rightHandSide_ne_nil (no degenerate rules).  The reverse word-to-Step direction is
-- not part of this gate (the free word monoid and toCode payload-collapse on universe codes make full
-- completeness non-derivable here).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.Step.toWordRewrite_rename

#assert_no_axioms FX1Poly.Core.StepStar.toWordRewrites_rename

#assert_no_axioms FX1Poly.Core.Step.toWordRewrite_subst

#assert_no_axioms FX1Poly.Core.fxStepSystem_rename_mem

#assert_no_axioms FX1Poly.Core.fxStepSystem_subst_mem

#assert_no_axioms FX1Poly.Core.fxStepSystem_imp_step

#assert_no_axioms FX1Poly.Core.fxStepSystem_leftHandSide_ne_nil

#assert_no_axioms FX1Poly.Core.fxStepSystem_rightHandSide_ne_nil

end FX1PolyAudit
