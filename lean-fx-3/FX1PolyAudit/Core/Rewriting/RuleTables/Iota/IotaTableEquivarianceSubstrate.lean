import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableEquivarianceSubstrate

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaTableEquivarianceSubstrate

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableEquivarianceSubstrate`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.iterateLiftRawSubst_zero

#assert_no_axioms FX1Poly.Core.iterateLiftRawSubst_succ

#assert_no_axioms FX1Poly.Core.ScopedChild.substView

#assert_no_axioms FX1Poly.Core.listEntryAt?_map

#assert_no_axioms FX1Poly.Core.RawTermChildren.toScopedChildren_subst

#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftZero?_substView

#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftOne?_substView

#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftTwo?_substView

#assert_no_axioms FX1Poly.Core.RawTerm.weakenBy_subst

#assert_no_axioms FX1Poly.Core.RawTerm.subst_liftLift_renameLiftWeaken

#assert_no_axioms FX1Poly.Core.RawTerm.subst_liftLiftLift_renameLiftLiftWeaken

#assert_no_axioms FX1Poly.Core.RawTerm.weakenBodyUnderOneBinderBy_subst

#assert_no_axioms FX1Poly.Core.RawTerm.weakenBodyUnderTwoBindersBy_subst

#assert_no_axioms FX1Poly.Core.RawTermChildren.replaceChildAt?_subst

#assert_no_axioms FX1Poly.Core.RawTermChildren.subst_lift_weaken

#assert_no_axioms FX1Poly.Core.RawTermChildren.weakenSpineBy_subst

#assert_no_axioms FX1Poly.Core.iterateLiftRawSubst_fixesTemplateBinder

#assert_no_axioms FX1Poly.Core.optionBindEqSome

#assert_no_axioms FX1Poly.Core.PayloadSource.IsScopeUniform

#assert_no_axioms FX1Poly.Core.ReductTemplate.HasScopeUniformPayloads

#assert_no_axioms FX1Poly.Core.ReductTemplateSpine.HasScopeUniformPayloads

#assert_no_axioms FX1Poly.Core.SpineReplacements.HasScopeUniformPayloads

#assert_no_axioms FX1Poly.Core.ScrutineeSpec.IsScopeUniform

#assert_no_axioms FX1Poly.Core.ScrutineeSpecsAreScopeUniform

#assert_no_axioms FX1Poly.Core.singletonUnguardedSpec_isScopeUniform

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.IsScopeUniform

#assert_no_axioms FX1Poly.Core.PayloadSource.unitConstantApp_isScopeUniform

#assert_no_axioms FX1Poly.Core.quotRecMkIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.quotElimMkIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.truncRecIntroIotaRow_isScopeUniform

end FX1PolyAudit
