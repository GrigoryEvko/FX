import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1.LeanKernel.Name
import LeanFX2.FX1.LeanKernel.Level
import LeanFX2.FX1.LeanKernel.Expr
import LeanFX2.FX1.LeanKernel.Substitution
import LeanFX2.FX1.LeanKernel.Reduction
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools

/-! ## AuditEffects — 34 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.Effects.EffectLabel
#assert_no_axioms LeanFX2.Effects.EffectRow.Member
#assert_no_axioms LeanFX2.Effects.EffectRow.empty
#assert_no_axioms LeanFX2.Effects.EffectRow.singleton
#assert_no_axioms LeanFX2.Effects.EffectRow.subset
#assert_no_axioms LeanFX2.Effects.EffectRow.join
#assert_no_axioms LeanFX2.Effects.EffectRow.member_append_left
#assert_no_axioms LeanFX2.Effects.EffectRow.member_append_right
#assert_no_axioms LeanFX2.Effects.EffectRow.member_append_inv
#assert_no_axioms LeanFX2.Effects.EffectRow.subset_refl
#assert_no_axioms LeanFX2.Effects.EffectRow.subset_trans
#assert_no_axioms LeanFX2.Effects.EffectRow.empty_subset
#assert_no_axioms LeanFX2.Effects.EffectRow.join_subset_left
#assert_no_axioms LeanFX2.Effects.EffectRow.join_subset_right
#assert_no_axioms LeanFX2.Effects.EffectRow.join_least_upper_bound
#assert_no_axioms LeanFX2.Effects.EffectRow.join_idempotent_subset
#assert_no_axioms LeanFX2.Effects.EffectRow.join_commutes_subset
#assert_no_axioms LeanFX2.Effects.EffectRow.join_associates_subset
#assert_no_axioms LeanFX2.Effects.read_subset_writeRead
#assert_no_axioms LeanFX2.Effects.OperationSignature
#assert_no_axioms LeanFX2.Effects.CanPerform
#assert_no_axioms LeanFX2.Effects.CanPerform.mono
#assert_no_axioms LeanFX2.Effects.CanPerform.join_left
#assert_no_axioms LeanFX2.Effects.CanPerform.join_right
#assert_no_axioms LeanFX2.Effects.Action
#assert_no_axioms LeanFX2.Effects.Step
#assert_no_axioms LeanFX2.Effects.Step.mono
#assert_no_axioms LeanFX2.Effects.Step.join_left
#assert_no_axioms LeanFX2.Effects.Step.join_right
#assert_no_axioms LeanFX2.Effects.Step.result_deterministic
#assert_no_axioms LeanFX2.Effects.HandlerCase
#assert_no_axioms LeanFX2.Effects.Handles
#assert_no_axioms LeanFX2.Effects.Handles.to_step
#assert_no_axioms LeanFX2.Effects.Handles.result_deterministic

end LeanFX2.Tools
