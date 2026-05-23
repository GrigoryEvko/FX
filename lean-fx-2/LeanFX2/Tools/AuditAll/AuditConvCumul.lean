import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Reduction.CumulSubstCompat
import LeanFX2.Reduction.Cumul.SubstCompatCases
import LeanFX2.Reduction.Cumul.SubstCompatTerm
import LeanFX2.Reduction.Cumul.SubstCompatCong
import LeanFX2.Reduction.Cumul.SubstOuter
import LeanFX2.Reduction.Cumul.Promotion

namespace LeanFX2.Tools

/-! ## AuditConvCumul — 52 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.ConvCumul.betaModElimIntroCumul
#assert_no_axioms LeanFX2.ConvCumul.betaModElimIntroCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.intervalOppCong
#assert_no_axioms LeanFX2.ConvCumul.intervalMeetCong
#assert_no_axioms LeanFX2.ConvCumul.intervalJoinCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_intervalOpp_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_intervalMeet_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_intervalJoin_allais
#assert_no_axioms LeanFX2.ConvCumul.glueIntroCong
#assert_no_axioms LeanFX2.ConvCumul.glueElimCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_glueIntro_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_glueElim_allais
#assert_no_axioms LeanFX2.ConvCumul.transpCong
#assert_no_axioms LeanFX2.ConvCumul.betaTranspConstantTypeCumul
#assert_no_axioms LeanFX2.ConvCumul.hcompCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_transp_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_hcomp_allais
#assert_no_axioms LeanFX2.ConvCumul.oeqJCong
#assert_no_axioms LeanFX2.ConvCumul.oeqFunextCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_oeqRefl_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_oeqJ_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_oeqFunext_allais
#assert_no_axioms LeanFX2.ConvCumul.recordIntroCong
#assert_no_axioms LeanFX2.ConvCumul.recordProjCong
#assert_no_axioms LeanFX2.ConvCumul.betaRecordProjIntroCumul
#assert_no_axioms LeanFX2.ConvCumul.betaRecordProjIntroCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_recordIntro_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_recordProj_allais
#assert_no_axioms LeanFX2.ConvCumul.idStrictRecCong
#assert_no_axioms LeanFX2.ConvCumul.iotaIdStrictRecReflCumul
#assert_no_axioms LeanFX2.ConvCumul.iotaIdStrictRecReflCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_idStrictRefl_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_idStrictRec_allais
#assert_no_axioms LeanFX2.ConvCumul.equivAppCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_equivApp_allais
#assert_no_axioms LeanFX2.ConvCumul.refineIntroCong
#assert_no_axioms LeanFX2.ConvCumul.refineElimCong
#assert_no_axioms LeanFX2.ConvCumul.betaRefineElimIntroCumul
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_refineIntro_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_refineElim_allais
#assert_no_axioms LeanFX2.ConvCumul.codataUnfoldCong
#assert_no_axioms LeanFX2.ConvCumul.codataDestCong
#assert_no_axioms LeanFX2.ConvCumul.betaCodataDestUnfoldCumul
#assert_no_axioms LeanFX2.ConvCumul.betaCodataDestUnfoldCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_codataUnfold_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_codataDest_allais
#assert_no_axioms LeanFX2.ConvCumul.sessionSendCong
#assert_no_axioms LeanFX2.ConvCumul.sessionRecvCong
#assert_no_axioms LeanFX2.ConvCumul.effectPerformCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_sessionSend_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_sessionRecv_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_effectPerform_allais

/-! ## Structural recursion bases (refl / sym / trans) and Term-level
base arms (var / unit / cumulUp) — the load-bearing core of
`ConvCumul.subst_compatible`. -/

#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_refl
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_sym
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_trans
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_var
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_unit
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_cumulUp_term
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_outer
#assert_no_axioms LeanFX2.ConvCumul.viaUp_raw_eq

/-! ## cong subst-compatibility (Pattern 2+3 cong arms). -/

#assert_no_axioms LeanFX2.ConvCumul.appCong_subst_compatible
#assert_no_axioms LeanFX2.ConvCumul.cumulUpCong_subst_compatible
#assert_no_axioms LeanFX2.ConvCumul.fstCong_subst_compatible
#assert_no_axioms LeanFX2.ConvCumul.pairCong_subst_compatible
#assert_no_axioms LeanFX2.ConvCumul.sndCong_subst_compatible

/-! ## HoTT / cubical subst-compat arms (equiv / funext / ua / hcompPath). -/

#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_equivIntroHet_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_equivReflId_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_equivReflIdAtId_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_funextIntroHet_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_funextRefl_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_funextReflAtId_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_uaIntroHet_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_hcompPath_allais

/-! ## ConvCumul → Conv bridge family (`_toConv`) plus refl/sym/roundtrip
plumbing.  These thread the cross-level cumul relation back into the
homogeneous `Conv` relation that the conversion checker consumes. -/

#assert_no_axioms LeanFX2.ConvCumul.refl_toConv
#assert_no_axioms LeanFX2.ConvCumul.toConv_toConvCumul_refl
#assert_no_axioms LeanFX2.ConvCumul.sym_via_refl
#assert_no_axioms LeanFX2.ConvCumul.refl_inverse_identity
#assert_no_axioms LeanFX2.ConvCumul.refl_inverse_roundtrip_B
#assert_no_axioms LeanFX2.ConvCumul.betaApp_roundtrip_eq
#assert_no_axioms LeanFX2.ConvCumul.betaAppCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.betaAppPiCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.betaFstPairCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.betaSndPairCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.betaPathAppCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.betaGlueElimIntroCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaBoolElimTrueCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaBoolElimFalseCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaNatElimZeroCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaNatElimSuccCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaNatRecZeroCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaNatRecSuccCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaListElimNilCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaListElimConsCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaOptionMatchNoneCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaOptionMatchSomeCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaEitherMatchInlCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaEitherMatchInrCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.iotaIdJReflCumul_toConv

end LeanFX2.Tools
