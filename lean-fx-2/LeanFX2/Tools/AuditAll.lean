import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Term
import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.Bridge
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.ParRed
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Confluence.ConvBridge
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Bridge.PathToId
import LeanFX2.Bridge.IdToPath
import LeanFX2.Bridge.PathIdInverse
import LeanFX2.Reduction.Conv
import LeanFX2.Reduction.CumulAllais
import LeanFX2.Algo.WHNF
import LeanFX2.Cubical.Path
import LeanFX2.Cubical.PathLemmas
import LeanFX2.Cubical.Transport
import LeanFX2.HoTT.HIT.Eliminator
import LeanFX2.HoTT.HIT.PropTrunc
import LeanFX2.HoTT.HIT.SetTrunc
import LeanFX2.HoTT.HIT.Quot
import LeanFX2.HoTT.HIT.S1
import LeanFX2.HoTT.HIT.Suspension
import LeanFX2.HoTT.HIT.Pushout
import LeanFX2.HoTT.HIT.Coequalizer
import LeanFX2.HoTT.HIT.Examples
import LeanFX2.Graded.Rules
import LeanFX2.Graded.Term
import LeanFX2.Graded.AtkeyAttack
import LeanFX2.Graded.Dimensions21

/-! # Tools/AuditAll — build-failing zero-axiom gate

This file is intentionally executable: importing it runs
`#assert_no_axioms` over load-bearing kernel declarations.  Unlike
`#print axioms`, these gates fail elaboration when any dependency tree
contains an axiom, including Lean core axioms such as `propext`,
`Quot.sound`, or `Classical.choice`.

This is not yet a generated whole-namespace audit.  It is a curated
machine-enforced gate for the current coverage-gap list and typed D2.5
path / Glue parity slices.
-/

namespace LeanFX2.Tools

-- Raw partial-renaming foundation for safe weakening recognition
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

-- Typed D2.5 path-application parity
#assert_no_axioms LeanFX2.Term.toRaw_interval0
#assert_no_axioms LeanFX2.Term.toRaw_interval1
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
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_toRaw
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_typeLineRecognized
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_sourceCong
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_sourceCong_toRawBridge
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_sourceConvCumul
#assert_no_axioms LeanFX2.Step.par.pathLam
#assert_no_axioms LeanFX2.Step.par.pathApp
#assert_no_axioms LeanFX2.Step.par.betaPathApp
#assert_no_axioms LeanFX2.Step.par.betaPathAppDeep
#assert_no_axioms LeanFX2.Step.par.toRawBridge

-- Typed D2.5 Glue-elimination parity
#assert_no_axioms LeanFX2.Term.toRaw_glueIntro
#assert_no_axioms LeanFX2.Term.toRaw_glueElim
#assert_no_axioms LeanFX2.Step.par.glueIntro
#assert_no_axioms LeanFX2.Step.par.glueElim
#assert_no_axioms LeanFX2.Step.par.betaGlueElimIntro
#assert_no_axioms LeanFX2.Step.par.betaGlueElimIntroDeep
#assert_no_axioms LeanFX2.ConvCumul.glueIntroCong
#assert_no_axioms LeanFX2.ConvCumul.glueElimCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_glueIntro_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_glueElim_allais
#assert_no_axioms LeanFX2.Term.headCtor
#assert_no_axioms LeanFX2.Term.isWHNF

-- Typed D2.5 transport / hcomp congruence parity
#assert_no_axioms LeanFX2.Term.toRaw_transp
#assert_no_axioms LeanFX2.Term.toRaw_hcomp
#assert_no_axioms LeanFX2.Step.par.transp
#assert_no_axioms LeanFX2.Step.par.hcomp
#assert_no_axioms LeanFX2.ConvCumul.transpCong
#assert_no_axioms LeanFX2.ConvCumul.hcompCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_transp_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_hcomp_allais

-- Conv core
#assert_no_axioms LeanFX2.Conv.refl
#assert_no_axioms LeanFX2.Conv.fromStep
#assert_no_axioms LeanFX2.Conv.toRawJoin
#assert_no_axioms LeanFX2.Conv.canonicalRaw
#assert_no_axioms LeanFX2.Conv.transRaw

-- HoTT HIT setoid foundation
#assert_no_axioms LeanFX2.HoTT.HIT.EmptyPathLabel
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec.hasPathBetween
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec.discrete
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec.discrete_hasNoPath
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.preservesRelation
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.discrete
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.indiscrete
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.fromEquivalence
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.run
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.run_respects
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.constant
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.constant_run
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.intro
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.squash
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.rec
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.rec_intro
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.rec_squash
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.recConstant
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.recConstant_intro
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.intro
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.path
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.rec
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.rec_intro
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.rec_path
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.equality
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.intro
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.sound
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.rec
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.rec_intro
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.rec_sound
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.recConstant
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.recConstant_intro
#assert_no_axioms LeanFX2.HoTT.HIT.S1PointLabel
#assert_no_axioms LeanFX2.HoTT.HIT.S1PathLabel
#assert_no_axioms LeanFX2.HoTT.HIT.S1Spec
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loopSpec
#assert_no_axioms LeanFX2.HoTT.HIT.S1.setoid
#assert_no_axioms LeanFX2.HoTT.HIT.S1.base
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.rec
#assert_no_axioms LeanFX2.HoTT.HIT.S1.rec_base
#assert_no_axioms LeanFX2.HoTT.HIT.S1.rec_loop
#assert_no_axioms LeanFX2.HoTT.HIT.SuspensionPoint
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.setoid
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.north
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.south
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.meridian
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec_north
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec_south
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec_meridian
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutCarrier
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.evaluate
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.left
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.right
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.glue
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec_left
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec_right
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec_glue
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.point
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.equalize
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.rec
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.rec_point
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.rec_equalize
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.quotientUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.propTruncUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.setTruncUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.s1BaseUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.suspensionNorthUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.pushoutUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.pushoutLeftUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.coequalizerUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.coequalizerPointUnit

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
#assert_no_axioms LeanFX2.Graded.structuralDimensionEntries21_length
#assert_no_axioms LeanFX2.Graded.semiringDimensions21_length
#assert_no_axioms LeanFX2.Graded.semiringDimensionSlots21_length
#assert_no_axioms LeanFX2.Graded.joinDimensions21_length
#assert_no_axioms LeanFX2.Graded.joinDimensionSlots21_length
#assert_no_axioms LeanFX2.Graded.structuralDimensionSlots21_length
#assert_no_axioms LeanFX2.Graded.semiringDimensions21_slots_length_match
#assert_no_axioms LeanFX2.Graded.joinDimensions21_slots_length_match
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.bottom
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.one
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.le_refl
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.le_trans
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.joinGrades_bottom_le
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose_semiring_one_left
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose_semiring_one_right
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose_join_left_le
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose_join_right_le
#assert_no_axioms LeanFX2.Graded.JoinGradeVector.join_mono
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.join_mono
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose_mono

-- Loaded production namespace sweep.  `#audit_namespace` excludes
-- `LeanFX2.Tools` and `LeanFX2.Smoke`, so this is the broad fail-fast
-- gate for every production declaration imported above, not a
-- replacement for targeted smoke examples.
#audit_namespace LeanFX2

end LeanFX2.Tools
