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

/-! ## Audit chunk 01 (lines 34-145 of original AuditAll). -/

#assert_no_axioms LeanFX2.PartialRawRenaming
#assert_no_axioms LeanFX2.PartialRawRenaming.lift
#assert_no_axioms LeanFX2.PartialRawRenaming.dropNewest
#assert_no_axioms LeanFX2.PartialRawRenaming.dropNewest_weaken
#assert_no_axioms LeanFX2.PartialRawRenaming.lift_dropNewest_weaken_lift
#assert_no_axioms LeanFX2.Option.mapTwo
#assert_no_axioms LeanFX2.Option.mapThree
#assert_no_axioms LeanFX2.RawTerm.partialRename?
#assert_no_axioms LeanFX2.RawTerm.unweaken?
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?
#assert_no_axioms LeanFX2.RawTerm.unweaken?_newest_var_none
#assert_no_axioms LeanFX2.RawTerm.unweaken?_weaken_var
#assert_no_axioms LeanFX2.RawTerm.partialRename?_lift_preserves_binder_var
#assert_no_axioms LeanFX2.PartialRawRenaming.lift_rename_some
#assert_no_axioms LeanFX2.RawTerm.partialRename?_rename_some
#assert_no_axioms LeanFX2.RawTerm.unweaken?_weaken
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_weaken
#assert_no_axioms LeanFX2.RawTerm.unweaken?_pathLam_binder_var
#assert_no_axioms LeanFX2.RawTerm.unweaken?_pathLam_dropped_outer_var_none
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_interval_var_none
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_weaken_var
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_nested_binder_var
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_nested_interval_escape_none
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_unit_none

-- Term core
#assert_no_axioms LeanFX2.Term.subst
#assert_no_axioms LeanFX2.Term.rename
#assert_no_axioms LeanFX2.Term.toRaw_rename
#assert_no_axioms LeanFX2.Term.toRaw_subst
#assert_no_axioms LeanFX2.Term.toRaw_weaken
#assert_no_axioms LeanFX2.Term.toRaw_subst0
#assert_no_axioms LeanFX2.Term.toRaw_universeCode
#assert_no_axioms LeanFX2.Term.toRaw_cumulUp
#assert_no_axioms LeanFX2.Term.toRaw_equivReflId
#assert_no_axioms LeanFX2.Term.toRaw_funextRefl
#assert_no_axioms LeanFX2.Term.toRaw_equivReflIdAtId
#assert_no_axioms LeanFX2.Term.toRaw_funextReflAtId
#assert_no_axioms LeanFX2.Term.toRaw_equivIntroHet
#assert_no_axioms LeanFX2.Term.toRaw_uaIntroHet
#assert_no_axioms LeanFX2.Term.toRaw_funextIntroHet
#assert_no_axioms LeanFX2.Term.toRaw_arrowCode
#assert_no_axioms LeanFX2.Term.toRaw_piTyCode
#assert_no_axioms LeanFX2.Term.toRaw_sigmaTyCode
#assert_no_axioms LeanFX2.Term.toRaw_productCode
#assert_no_axioms LeanFX2.Term.toRaw_sumCode
#assert_no_axioms LeanFX2.Term.toRaw_listCode
#assert_no_axioms LeanFX2.Term.toRaw_optionCode
#assert_no_axioms LeanFX2.Term.toRaw_eitherCode
#assert_no_axioms LeanFX2.Term.toRaw_idCode
#assert_no_axioms LeanFX2.Term.toRaw_equivCode
#assert_no_axioms LeanFX2.Step.castSourceRaw
#assert_no_axioms LeanFX2.Step.castTargetRaw
#assert_no_axioms LeanFX2.Step.par.castSourceRaw
#assert_no_axioms LeanFX2.Step.par.castTargetRaw

-- Confluence core
#assert_no_axioms LeanFX2.RawStep.par.cd_lemma
#assert_no_axioms LeanFX2.RawStep.par.diamond
#assert_no_axioms LeanFX2.RawStep.par.glueElim_inv
#assert_no_axioms LeanFX2.RawStep.par.pathLam_inv

-- Raw D2.5 cubical beta rules
#assert_no_axioms LeanFX2.RawStep.par.betaPathApp
#assert_no_axioms LeanFX2.RawStep.par.betaPathAppDeep
#assert_no_axioms LeanFX2.RawStep.par.betaGlueElimIntro
#assert_no_axioms LeanFX2.RawStep.par.betaGlueElimIntroDeep
#assert_no_axioms LeanFX2.RawStep.par.betaModElimIntro
#assert_no_axioms LeanFX2.RawStep.par.betaModElimIntroDeep
#assert_no_axioms LeanFX2.RawTerm.cdModElimCase
#assert_no_axioms LeanFX2.RawStep.par.betaCodataDestUnfold
#assert_no_axioms LeanFX2.RawStep.par.betaCodataDestUnfoldDeep
#assert_no_axioms LeanFX2.RawTerm.cdCodataDestCase

-- Typed D2.5 path-application parity
#assert_no_axioms LeanFX2.Term.toRaw_interval0
#assert_no_axioms LeanFX2.Term.toRaw_interval1
#assert_no_axioms LeanFX2.Term.toRaw_intervalOpp
#assert_no_axioms LeanFX2.Term.toRaw_intervalMeet
#assert_no_axioms LeanFX2.Term.toRaw_intervalJoin
#assert_no_axioms LeanFX2.Term.toRaw_pathLam
#assert_no_axioms LeanFX2.Term.toRaw_pathApp
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
#assert_no_axioms LeanFX2.Bridge.constantPathToId
#assert_no_axioms LeanFX2.Bridge.constantPathToId_toRaw
#assert_no_axioms LeanFX2.Bridge.constantPathToId_onCanonical
#assert_no_axioms LeanFX2.Bridge.reflIdToConstantPath
#assert_no_axioms LeanFX2.Bridge.reflIdToConstantPath_toRaw
#assert_no_axioms LeanFX2.Bridge.reflIdToConstantPath_onRefl
#assert_no_axioms LeanFX2.Bridge.constantPath_roundTrip_onCanonical
#assert_no_axioms LeanFX2.Bridge.reflId_roundTrip_onRefl
#assert_no_axioms LeanFX2.Bridge.constantPath_roundTrip_toRaw
#assert_no_axioms LeanFX2.Bridge.reflId_roundTrip_toRaw
#assert_no_axioms LeanFX2.Bridge.pathToIdMeta
#assert_no_axioms LeanFX2.Bridge.idToPathMeta
#assert_no_axioms LeanFX2.Bridge.idToPathMeta_pathToIdMeta
#assert_no_axioms LeanFX2.Bridge.pathToIdMeta_idToPathMeta
#assert_no_axioms LeanFX2.Bridge.pathIdEquivMeta
#assert_no_axioms LeanFX2.Bridge.pathIdEquivMeta_toFun
#assert_no_axioms LeanFX2.Bridge.pathIdEquivMeta_invFun

end LeanFX2.Tools
