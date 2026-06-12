import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StepTableEquivariance
import FX1Poly.Core.StepTableRenameReflection

/-! # FX1PolyAudit/AuditIotaTableEquivariance — IOTA-T2 audit shard (substrate + headline)

Per-declaration zero-axiom gate for IOTA-T2: the fold-engine lift-iterate pins, the shift-erased
view under substitution (substView / lookup-map / per-shift projections), the depth-weakening
naturality (term, one-binder body, two-binder body — with the under-binder naturality squares),
slot-replacement naturality, the payload scope-uniformity certificate layer with all 18 row pins,
and the HEADLINE: the mutual template/spine/replacements interpretation naturality square plus the
depth-0 `interpretTarget?_subst` corollary — substitution equivariance for the whole iota-rule
table interpreter, conditional only on the per-row scope-uniformity certificates.  Every
declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Lift-iterate pins -/

#assert_no_axioms FX1Poly.Core.iterateLiftRawSubst_zero
#assert_no_axioms FX1Poly.Core.iterateLiftRawSubst_succ

/-! ## The shift-erased view under substitution -/

#assert_no_axioms FX1Poly.Core.ScopedChild.substView
#assert_no_axioms FX1Poly.Core.listEntryAt?_map
#assert_no_axioms FX1Poly.Core.RawTermChildren.toScopedChildren_subst
#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftZero?_substView
#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftOne?_substView
#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftTwo?_substView

/-! ## Depth-weakening naturality -/

#assert_no_axioms FX1Poly.Core.RawTerm.weakenBy_subst
#assert_no_axioms FX1Poly.Core.RawTerm.subst_liftLift_renameLiftWeaken
#assert_no_axioms FX1Poly.Core.RawTerm.subst_liftLiftLift_renameLiftLiftWeaken
#assert_no_axioms FX1Poly.Core.RawTerm.weakenBodyUnderOneBinderBy_subst
#assert_no_axioms FX1Poly.Core.RawTerm.weakenBodyUnderTwoBindersBy_subst

/-! ## Slot replacement naturality -/

#assert_no_axioms FX1Poly.Core.RawTermChildren.replaceChildAt?_subst

/-! ## Spine weakening naturality + boundVar fixpoint + bind splitter -/

#assert_no_axioms FX1Poly.Core.RawTermChildren.subst_lift_weaken
#assert_no_axioms FX1Poly.Core.RawTermChildren.weakenSpineBy_subst
#assert_no_axioms FX1Poly.Core.iterateLiftRawSubst_fixesTemplateBinder
#assert_no_axioms FX1Poly.Core.optionBindEqSome

/-! ## Payload scope-uniformity certificates -/

#assert_no_axioms FX1Poly.Core.PayloadSource.IsScopeUniform
#assert_no_axioms FX1Poly.Core.ReductTemplate.HasScopeUniformPayloads
#assert_no_axioms FX1Poly.Core.ReductTemplateSpine.HasScopeUniformPayloads
#assert_no_axioms FX1Poly.Core.SpineReplacements.HasScopeUniformPayloads
#assert_no_axioms FX1Poly.Core.ScrutineeSpec.IsScopeUniform
#assert_no_axioms FX1Poly.Core.ScrutineeSpecsAreScopeUniform
#assert_no_axioms FX1Poly.Core.singletonUnguardedSpec_isScopeUniform
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.IsScopeUniform
#assert_no_axioms FX1Poly.Core.PayloadSource.unitConstantApp_isScopeUniform

/-! ## The 18 row certificates -/

#assert_no_axioms FX1Poly.Core.betaIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.boolTrueIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.boolFalseIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.fstPairIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.sndPairIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.natElimZeroIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.natRecZeroIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.natRecSuccIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.listElimNilIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.listElimConsIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.optionMatchNoneIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.optionMatchSomeIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.eitherMatchInlIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.eitherMatchInrIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.idJReflIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.idStrictRecReflIotaRow_isScopeUniform
#assert_no_axioms FX1Poly.Core.pathBetaIotaRow_isScopeUniform

/-! ## Option pins + cast composition -/

#assert_no_axioms FX1Poly.Core.optionSomeBindMonadic
#assert_no_axioms FX1Poly.Core.optionSomeBindExplicit
#assert_no_axioms FX1Poly.Core.optionSomeMap
#assert_no_axioms FX1Poly.Core.optionMapEqSome
#assert_no_axioms FX1Poly.Core.castCompose

/-! ## Per-stage interpreter naturality -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeTermAt?_subst
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeChildLookup_subst
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.elimPayloadAtDepth?_subst
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.resolvePayloadSource?_subst

/-! ## The HEADLINE: interpretation naturality (mutual trio + depth-0 corollary) -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?_subst
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretBuiltChildren?_subst
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretReplacements?_subst
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTarget?_subst

/-! ## Firing-dispatcher naturality -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires_subst
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineesFire_subst
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?_subst

/-! ## Relation closure: the table relation substitutes -/

#assert_no_axioms FX1Poly.Core.StepOverTable.subst
#assert_no_axioms FX1Poly.Core.StepOverTableChildren.subst
#assert_no_axioms FX1Poly.Core.iotaRuleTable_isScopeUniform
#assert_no_axioms FX1Poly.Core.StepTable.subst

/-! ## Rename-as-subst factoring + rename closure -/

#assert_no_axioms FX1Poly.Core.RawTermSubst.ofRenaming
#assert_no_axioms FX1Poly.Core.RawTermSubst.ofRenaming_lift_pointwise
#assert_no_axioms FX1Poly.Core.RawTermSubst.ofRenaming_iterateLift_pointwise
#assert_no_axioms FX1Poly.Core.RawTerm.rename_eq_subst_ofRenaming
#assert_no_axioms FX1Poly.Core.RawTermChildren.rename_eq_subst_ofRenaming
#assert_no_axioms FX1Poly.Core.StepOverTable.rename
#assert_no_axioms FX1Poly.Core.StepTable.rename

/-! ## Rename REFLECTION: the pattern test reflects (backward direction) -/

#assert_no_axioms FX1Poly.Core.scrutineeSlotLookup_rename
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires_reflectRename
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineesFire_reflectRename

/-! ## Stage EQUATIONS at the rename instantiation (two-sided forms) -/

#assert_no_axioms FX1Poly.Core.RawTerm.rename_var_reduces
#assert_no_axioms FX1Poly.Core.RawTerm.scopedChildrenView_rename
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeTermAt?_rename
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeChildrenAt?_rename
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.elimPayloadAtDepth?_rename
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.resolvePayloadSource?_rename

/-! ## Interpreter NONE-preservation walk + the headline rename equations -/

#assert_no_axioms FX1Poly.Core.scopedChildAt?_rename
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?_rename_none
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretBuiltChildren?_rename_none
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretReplacements?_rename_none
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?_rename
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTarget?_rename
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?_rename

end FX1PolyAudit
