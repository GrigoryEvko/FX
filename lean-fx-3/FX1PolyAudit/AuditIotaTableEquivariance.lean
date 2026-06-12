import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.IotaTableEquivarianceSubstrate

/-! # FX1PolyAudit/AuditIotaTableEquivariance — IOTA-T2 audit shard (equivariance substrate)

Per-declaration zero-axiom gate for the IOTA-T2 substrate: the fold-engine lift-iterate pins, the
shift-erased view under substitution (substView / lookup-map / per-shift projections), the
depth-weakening naturality (term, one-binder body, two-binder body — with the under-binder naturality
squares), and slot-replacement naturality.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

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

end FX1PolyAudit
