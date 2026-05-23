import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2.Cubical.Composition
import LeanFX2.Cubical.Glue
import LeanFX2.Cubical.Transport
import LeanFX2.Cubical.Ua
import LeanFX2.HoTT.Equivalence
import LeanFX2.HoTT.Funext
import LeanFX2.HoTT.FunextFull
import LeanFX2.HoTT.Path.Groupoid
import LeanFX2.HoTT.Univalence
import LeanFX2.HoTT.Identity
import LeanFX2.HoTT.Observational

namespace LeanFX2.Tools

/-! ## AuditCubical — 90 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.Cubical.constantPath
#assert_no_axioms LeanFX2.Cubical.constantPath_toRaw
#assert_no_axioms LeanFX2.Cubical.constantTypePath
#assert_no_axioms LeanFX2.Cubical.constantTypePath_toRaw
#assert_no_axioms LeanFX2.Cubical.constantPath_rawRecognized
#assert_no_axioms LeanFX2.Cubical.constantTypePath_rawRecognized
#assert_no_axioms LeanFX2.Cubical.intervalBinderPath
#assert_no_axioms LeanFX2.Cubical.intervalBinderPath_rawRejected
#assert_no_axioms LeanFX2.Cubical.constantPath_rawBetaApp
#assert_no_axioms LeanFX2.Cubical.constantPath_betaPathApp
#assert_no_axioms LeanFX2.Cubical.constantPath_betaPathApp_toRawEndpoint
#assert_no_axioms LeanFX2.Cubical.constantTypePath_betaPathApp
#assert_no_axioms LeanFX2.Cubical.constantTypePath_betaPathApp_toRawEndpoint
#assert_no_axioms LeanFX2.Cubical.constantPathToObservationalId
#assert_no_axioms LeanFX2.Cubical.constantPathToObservationalId_toRaw
#assert_no_axioms LeanFX2.Cubical.constantPathToObservationalId_onCanonical
#assert_no_axioms LeanFX2.Cubical.observationalReflToConstantPath
#assert_no_axioms LeanFX2.Cubical.observationalReflToConstantPath_toRaw
#assert_no_axioms LeanFX2.Cubical.constantCubicalTypePathToEquiv
#assert_no_axioms LeanFX2.Cubical.constantCubicalTypePathToEquiv_toRaw
#assert_no_axioms LeanFX2.Cubical.constantCubicalTypePathToEquiv_onCanonical
#assert_no_axioms LeanFX2.Cubical.pathIdMetaEquiv
#assert_no_axioms LeanFX2.Cubical.uaReflConv
#assert_no_axioms LeanFX2.Cubical.uaHetConv
#assert_no_axioms LeanFX2.Cubical.uaConstantTypePathToEquiv
#assert_no_axioms LeanFX2.Cubical.uaConstantTypePathToEquiv_toRaw
#assert_no_axioms LeanFX2.Cubical.uaConstantTypePathToEquiv_onCanonical
#assert_no_axioms LeanFX2.Cubical.uaBetaMeta
#assert_no_axioms LeanFX2.Cubical.uaBetaMetaRefl
#assert_no_axioms LeanFX2.Cubical.uaBetaMetaSymm
#assert_no_axioms LeanFX2.Cubical.uaTransportViaReflEquiv
#assert_no_axioms LeanFX2.Cubical.uaKernelRflAlignsWithMeta
#assert_no_axioms LeanFX2.Cubical.glueIntroduction
#assert_no_axioms LeanFX2.Cubical.glueIntroduction_toRaw
#assert_no_axioms LeanFX2.Cubical.glueElimination
#assert_no_axioms LeanFX2.Cubical.glueElimination_toRaw
#assert_no_axioms LeanFX2.Cubical.glueIntroduction_parCong
#assert_no_axioms LeanFX2.Cubical.glueElimination_parCong
#assert_no_axioms LeanFX2.Cubical.glueIntroduction_convCumul
#assert_no_axioms LeanFX2.Cubical.glueElimination_convCumul
#assert_no_axioms LeanFX2.Cubical.glueElimIntro_parBeta
#assert_no_axioms LeanFX2.Cubical.glueElimIntro_convCumulBeta
#assert_no_axioms LeanFX2.Cubical.homogeneousComposition
#assert_no_axioms LeanFX2.Cubical.homogeneousComposition_toRaw
#assert_no_axioms LeanFX2.Cubical.homogeneousComposition_parCong
#assert_no_axioms LeanFX2.Cubical.homogeneousComposition_convCumul
#assert_no_axioms LeanFX2.Cubical.degenerateHomogeneousComposition
#assert_no_axioms LeanFX2.Cubical.degenerateHomogeneousComposition_toRaw
#assert_no_axioms LeanFX2.Cubical.degenerateHomogeneousComposition_parCong
#assert_no_axioms LeanFX2.Cubical.degenerateHomogeneousComposition_convCumul
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_toRaw
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_typeLineRecognized
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_sourceCong
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_sourceCong_toRawBridge
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_sourceConvCumul
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_betaParStep
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_betaParStep_toRawBridge
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_betaParStar
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_betaConvCumul
#assert_no_axioms LeanFX2.Equiv
#assert_no_axioms LeanFX2.IsContr
#assert_no_axioms LeanFX2.IsEquiv
#assert_no_axioms LeanFX2.Fiber
#assert_no_axioms LeanFX2.Equiv.refl
#assert_no_axioms LeanFX2.Equiv.symm
#assert_no_axioms LeanFX2.Equiv.trans
#assert_no_axioms LeanFX2.Equiv.trans_refl_left_toFun
#assert_no_axioms LeanFX2.Equiv.trans_refl_right_toFun
#assert_no_axioms LeanFX2.IsContr.unit
#assert_no_axioms LeanFX2.IsEquiv.identity
#assert_no_axioms LeanFX2.Univalence
#assert_no_axioms LeanFX2.UnivalenceHet
#assert_no_axioms LeanFX2.Univalence.idToEquivMeta
#assert_no_axioms LeanFX2.Univalence.idToEquivMeta_isEquiv_toFun
#assert_no_axioms LeanFX2.Univalence.idToEquivMeta_isEquiv_invFun
#assert_no_axioms LeanFX2.Univalence.ua_beta_meta
#assert_no_axioms LeanFX2.Univalence.ua_beta_toFun_pointwise
#assert_no_axioms LeanFX2.Univalence.ua_beta_invFun_pointwise
#assert_no_axioms LeanFX2.funext
#assert_no_axioms LeanFX2.FunextHet
#assert_no_axioms LeanFX2.Funext.fnEqToPointwiseMeta
#assert_no_axioms LeanFX2.Funext.pointwiseMetaToFnEqAtRefl
#assert_no_axioms LeanFX2.Funext.kernelMetaCorrespondence_atRefl
#assert_no_axioms LeanFX2.Path.trans
#assert_no_axioms LeanFX2.Path.symm
#assert_no_axioms LeanFX2.Path.trans_assoc
#assert_no_axioms LeanFX2.Path.trans_refl_left
#assert_no_axioms LeanFX2.Path.trans_refl_right
#assert_no_axioms LeanFX2.Path.symm_symm
#assert_no_axioms LeanFX2.Path.trans_symm_left
#assert_no_axioms LeanFX2.Path.trans_symm_right
#assert_no_axioms LeanFX2.Path.symm_trans
#assert_no_axioms LeanFX2.PathGroupoidLaws
#assert_no_axioms LeanFX2.PathGroupoidLaws.instance
#assert_no_axioms LeanFX2.Path.trans_left_cancel
#assert_no_axioms LeanFX2.Path.trans_right_cancel

/-! ## Identity-type ι rule (`J base (refl x) ⟶ base`) — the
identity eliminator computation rule.  Per the project's
HIT/identity-eliminator commitment these must be axiom-clean. -/

#assert_no_axioms LeanFX2.Step.idJ_refl
#assert_no_axioms LeanFX2.Conv.idJ_refl_baseCase

/-! ## Observational-equality eliminator family (`HoTT/Observational.lean`).
The equivalence-relation laws, function congruence, transport,
substitution, and structured-type decomposition rules. -/

#assert_no_axioms LeanFX2.OEq.refl
#assert_no_axioms LeanFX2.OEq.sym
#assert_no_axioms LeanFX2.OEq.trans
#assert_no_axioms LeanFX2.OEq.cong
#assert_no_axioms LeanFX2.OEq.cong2
#assert_no_axioms LeanFX2.OEq.transport
#assert_no_axioms LeanFX2.OEq.subst
#assert_no_axioms LeanFX2.OEqDecomposeProd.to_components
#assert_no_axioms LeanFX2.OEqDecomposeProd.from_components
#assert_no_axioms LeanFX2.OEqDecomposeSum.inl_components
#assert_no_axioms LeanFX2.OEqDecomposeSum.inr_components
#assert_no_axioms LeanFX2.OEqDecomposeSum.inl_inr_impossible
#assert_no_axioms LeanFX2.OEqDecomposePiSetWise.to_pointwise
#assert_no_axioms LeanFX2.OEqUIP.uip_set
#assert_no_axioms LeanFX2.OEqType.to_equiv

end LeanFX2.Tools
