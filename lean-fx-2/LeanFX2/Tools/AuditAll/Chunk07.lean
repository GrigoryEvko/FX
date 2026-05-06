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

/-! ## Audit chunk 07 (lines 706-817 of original AuditAll). -/

#assert_no_axioms LeanFX2.Codata.Stream.Step.head_respects_bisim
#assert_no_axioms LeanFX2.Codata.Stream.Step.tail_respects_bisim
#assert_no_axioms LeanFX2.Codata.Stream.Step.head_unfold
#assert_no_axioms LeanFX2.Codata.Stream.Step.tail_unfold_bisim
#assert_no_axioms LeanFX2.Codata.Stream.Productive
#assert_no_axioms LeanFX2.Codata.Stream.productive_of_stream
#assert_no_axioms LeanFX2.Codata.Stream.productive_head
#assert_no_axioms LeanFX2.Codata.Stream.productive_tail
#assert_no_axioms LeanFX2.Codata.Stream.productive_unfold
#assert_no_axioms LeanFX2.Codata.Stream.productive_of_bisim

-- Effect row structural layer
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

-- Session protocol structural layer
#assert_no_axioms LeanFX2.SessionProtocol
#assert_no_axioms LeanFX2.SessionProtocol.depth
#assert_no_axioms LeanFX2.SessionProtocol.isFinite
#assert_no_axioms LeanFX2.SessionProtocol.isFinite_of_tree
#assert_no_axioms LeanFX2.SessionProtocol.isFiniteDecidable
#assert_no_axioms LeanFX2.SessionProtocol.isFinite.decidable
#assert_no_axioms LeanFX2.SessionProtocol.dual
#assert_no_axioms LeanFX2.SessionProtocol.dual_end
#assert_no_axioms LeanFX2.SessionProtocol.dual_involutive
#assert_no_axioms LeanFX2.SessionProtocol.Action
#assert_no_axioms LeanFX2.SessionProtocol.Action.dual
#assert_no_axioms LeanFX2.SessionProtocol.Action.dual_involutive
#assert_no_axioms LeanFX2.SessionProtocol.Action.dual_injective
#assert_no_axioms LeanFX2.SessionProtocol.Step
#assert_no_axioms LeanFX2.SessionProtocol.Step.preserves_isFinite
#assert_no_axioms LeanFX2.SessionProtocol.Step.dual
#assert_no_axioms LeanFX2.SessionProtocol.Step.not_from_end
#assert_no_axioms LeanFX2.SessionProtocol.Step.target_deterministic
#assert_no_axioms LeanFX2.SessionProtocol.Step.of_dual
#assert_no_axioms LeanFX2.SessionProtocol.Step.dual_iff
#assert_no_axioms LeanFX2.SessionGlobal
#assert_no_axioms LeanFX2.SessionGlobal.isWellFormed
#assert_no_axioms LeanFX2.SessionGlobal.transmit_self_not_isWellFormed
#assert_no_axioms LeanFX2.SessionGlobal.choice_self_not_isWellFormed
#assert_no_axioms LeanFX2.SessionGlobal.Projects
#assert_no_axioms LeanFX2.SessionGlobal.Projects.local_isFinite

-- Graded core
#assert_no_axioms LeanFX2.Graded.GradeVector.add_mono
#assert_no_axioms LeanFX2.Graded.GradeVector.mul_mono
#assert_no_axioms LeanFX2.Graded.GradeAttribution.add_mono
#assert_no_axioms LeanFX2.Graded.GradeAttribution.scaleBy_mono
#assert_no_axioms LeanFX2.Graded.GradedCtx.le
#assert_no_axioms LeanFX2.Graded.GradedCtx.le_refl
#assert_no_axioms LeanFX2.Graded.GradedCtx.le_trans
#assert_no_axioms LeanFX2.Graded.IsLamCompatible
#assert_no_axioms LeanFX2.Graded.IsLamCompatibleWithAvailable
#assert_no_axioms LeanFX2.Graded.IsLamCompatibleWithAvailable.available_mono
#assert_no_axioms LeanFX2.Graded.GradeAttribution.scaleBy
#assert_no_axioms LeanFX2.Graded.IsAppCompatible.mono
#assert_no_axioms LeanFX2.Graded.IsLetCompatible.mono
#assert_no_axioms LeanFX2.Graded.IsIfCompatible.mono
#assert_no_axioms LeanFX2.Graded.GradedCtx.toCtx
#assert_no_axioms LeanFX2.Graded.GradedTerm
#assert_no_axioms LeanFX2.Graded.GradedTerm.unit
#assert_no_axioms LeanFX2.Graded.GradedTerm.boolTrue
#assert_no_axioms LeanFX2.Graded.GradedTerm.boolFalse
#assert_no_axioms LeanFX2.Graded.GradedTerm.var
#assert_no_axioms LeanFX2.Graded.GradedTerm.lam
#assert_no_axioms LeanFX2.Graded.GradedTerm.app
#assert_no_axioms LeanFX2.Graded.GradedTerm.boolElim
#assert_no_axioms LeanFX2.Graded.GradedTerm.subsumeGrade
#assert_no_axioms LeanFX2.Graded.GradedTerm.underlying_toRaw

-- Dimensions21 registry and aggregate carrier operations
#assert_no_axioms LeanFX2.Graded.allDimensionSlots_length
#assert_no_axioms LeanFX2.Graded.semiringDimensionEntries21
#assert_no_axioms LeanFX2.Graded.joinDimensionEntries21
#assert_no_axioms LeanFX2.Graded.structuralDimensionEntries21
#assert_no_axioms LeanFX2.Graded.semiringDimensionSlots21
#assert_no_axioms LeanFX2.Graded.joinDimensionSlots21
#assert_no_axioms LeanFX2.Graded.structuralDimensionSlots21
#assert_no_axioms LeanFX2.Graded.semiringDimensionEntries21_length
#assert_no_axioms LeanFX2.Graded.joinDimensionEntries21_length

end LeanFX2.Tools
