import FX1PolyAudit.AuditGen
-- Sink files of the foundational term-substrate slice (importing these
-- transitively loads every FX1Poly.Core declaration).
import FX1Poly.Core.CheckResult
import FX1Poly.Core.ConsistencyStrength
import FX1Poly.Core.CoreFxProfile
import FX1Poly.Core.FoldShiftGreaterThanOne
import FX1Poly.Core.GenPayloadEvidence
import FX1Poly.Core.GeneratorChildSpecsDim0
import FX1Poly.Core.GeneratorTotalityClass
import FX1Poly.Core.HasEqualDim
import FX1Poly.Core.RawCellCascadeLaws
import FX1Poly.Core.RawCellCode
import FX1Poly.Core.RawTermSubstAction
import FX1Poly.Core.RawTermChildrenUnique
import FX1Poly.Core.RuleSpec
import FX1Poly.Core.SiteOpenness
import FX1Poly.Core.StepEta
import FX1Poly.Core.StepInversion
import FX1Poly.Core.HeadStep
import FX1Poly.Core.HeadStepCommute
import FX1Poly.Core.HeadStepCommute2
import FX1Poly.Core.HeadStepRenameReflect
import FX1Poly.Core.IotaHeadStep
import FX1Poly.Core.IotaHeadStepDisjoint
import FX1Poly.Core.WeakHeadStep
import FX1Poly.Core.WeakHeadStepDeterministic
import FX1Poly.Core.WeakHeadStepSubsumes
import FX1Poly.Core.WeakHeadStepNormalForms
import FX1Poly.Core.WeakHeadStepSubst
import FX1Poly.Core.WeakHeadStepRename
import FX1Poly.Core.WeakHeadStepRenameReflect
import FX1Poly.Core.StepRenameReflect
import FX1Poly.Core.WeakHeadStepCommute
import FX1Poly.Core.WeakHeadNormalPreservation
import FX1Poly.Core.ReducibleTypeForwardClosure
import FX1Poly.Core.ReducibleTypeForwardStepStar
import FX1Poly.Core.ReducibleTypeConvInvariance
import FX1Poly.Core.DependentArrowReducibilityCandidate
import FX1Poly.Core.ReducibleTypeReducibilityCandidate
import FX1Poly.Core.ReducibleMember
import FX1Poly.Core.ReducibleMemberNeutral
import FX1Poly.Core.ReducibleTypeWellFormed
import FX1Poly.Core.StratifiedReducibleType
import FX1Poly.Core.StratifiedReducibleTypeRename
import FX1Poly.Core.KripkeCandidateRenameClosure
import FX1Poly.Core.NeutralTermRename
import FX1Poly.Core.StratifiedReducibleTypeForwardClosure
import FX1Poly.Core.StratifiedReducibleTypeCandidate
import FX1Poly.Core.StratifiedReducibleTypeNeutral
import FX1Poly.Core.StratifiedReducibleTypeConvInvariance
import FX1Poly.Core.StratifiedReducibleTypeReducibilityCandidate
import FX1Poly.Core.StratifiedReducibleTypeHeadExpansion
import FX1Poly.Core.StratifiedReducibleMember
import FX1Poly.Core.StratifiedReducibleMemberNeutral
import FX1Poly.Core.StrongNormalizationReflection
import FX1Poly.Core.StratifiedReducibleMemberAbstraction
import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StratifiedReducibleMemberNonDependent
import FX1Poly.Core.StratifiedReducibleSmoke
import FX1Poly.Core.ArrowCandidateMembership
import FX1Poly.Core.CandidateInterpretationFundamental
import FX1Poly.Core.RawTermSubstConsCommute
-- Certifier base (CellBoundary / PolyCell + immediate consumers).
import FX1Poly.Core.CertifiedRawCell
import FX1Poly.Core.CertifiedTermSpineProjections
import FX1Poly.Core.CertifyChildSpine
import FX1Poly.Core.PolyCellErasure
import FX1Poly.Core.PolyCellHelpers
-- Certifier spine + exact-cell builders.
import FX1Poly.Core.CertifyRawCellExact
import FX1Poly.Core.CertifyTermSpine
import FX1Poly.Core.SpineRenameStep
import FX1Poly.Core.SpineSubstStep
-- Certifier coverage / general inference + certified-term to PolyCell.
import FX1Poly.Core.CertifyRawCellExactCompHRejects
import FX1Poly.Core.CertifyRawCellExactShape
import FX1Poly.Core.CertifyRawCellExactSound
import FX1Poly.Core.CertifyRawCellExactTermBase
import FX1Poly.Core.CertifyRawCellExactWrongChildShape
import FX1Poly.Core.CertifyRawCellExactRenameEquiv
import FX1Poly.Core.CertifyRawCellExactNegativeProbes
import FX1Poly.Core.CertifyTermExact
import FX1Poly.Core.CheckRawCellAs
import FX1Poly.Core.InferRawCellGeneralSound
import FX1Poly.Core.InferRawCellGeneralAcceptedCellDimensionEq
import FX1Poly.Core.CertifiedToPolyCell
-- HasCertified intro/composition/projection + subject-reduction iota family
-- + beta-redex preservation + structural-induction primitives + Pair layer.
import FX1Poly.Core.HasCertifiedHonestyProbes
import FX1Poly.Core.SubjectReductionBaseIotas
import FX1Poly.Core.SubjectReductionEtaStructural
import FX1Poly.Core.SubjectReductionIotaBoolFalse
import FX1Poly.Core.SubjectReductionIotaBoolTrue
import FX1Poly.Core.SubjectReductionIotaEither
import FX1Poly.Core.SubjectReductionIotaIdRefl
import FX1Poly.Core.SubjectReductionIotaNatRec
import FX1Poly.Core.SubjectReductionIotaOption
import FX1Poly.Core.SubjectReductionIotaProjections
import FX1Poly.Core.CompoundRenamePreservation
import FX1Poly.Core.CompoundSubstPreservation
import FX1Poly.Core.RawTermFoldNonVarCommute
import FX1Poly.Core.BetaRedexDoublingSpike
import FX1Poly.Core.StructuralInductionPrimitives
import FX1Poly.Core.PairEliminatorLayer
-- Reduction machinery: raw NF/free-vars/fresh, Step subst/rename + HCC
-- wrappers + helper smokes, substitution-preservation mutual, Nat/Bool layers.
import FX1Poly.Core.RawTermNF
import FX1Poly.Core.StepRename
import FX1Poly.Core.StepHelperSmokes
import FX1Poly.Core.SubstPreservationMutual
import FX1Poly.Core.NatEliminatorLayer
import FX1Poly.Core.StructuralInductionWrapper
import FX1Poly.Core.StepHCCWrappers
-- Confluence + critical pairs + Conv congruence/subst-rename + StepPreservesShape
-- + remaining dim-0 eliminators (Id) + StepStarLength.
import FX1Poly.Core.ConvCongruence
import FX1Poly.Core.ConvSubstRename
import FX1Poly.Core.StepStarConfluence
import FX1Poly.Core.StepStarLength
import FX1Poly.Core.ConvNormalForm
import FX1Poly.Core.StepEtaEtaCriticalPairs
import FX1Poly.Core.StepIotaEtaInsideBinder
import FX1Poly.Core.StepBetaEtaPreservesShape
import FX1Poly.Core.SubjectReductionEtaBinder
import FX1Poly.Core.IdEliminatorLayer
-- Strong normalization (leaves/neutral/constructors/redexes/eta) + beta-eta
-- confluence + iota-eta double strips + concrete neutral predicate.
import FX1Poly.Core.NeutralTerm
import FX1Poly.Core.ReducibilityCandidate
import FX1Poly.Core.ReducibilityCandidateArrow
import FX1Poly.Core.NeutralStepClosure
import FX1Poly.Core.StrongNormalizationRedexes
import FX1Poly.Core.StrongNormalizationIotaRedexes
import FX1Poly.Core.BoolElimStrongNormalization
import FX1Poly.Core.IdentityEliminatorStrongNormalization
import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationSpineExpansion
import FX1Poly.Core.HeadExpansionClosure
import FX1Poly.Core.CandidateInterpretation
import FX1Poly.Core.CandidateInterpretationDeterminism
import FX1Poly.Core.CandidateInterpretationRename
import FX1Poly.Core.CandidateInterpretationSubst
import FX1Poly.Core.CandidateInterpretationHeadExpansion
import FX1Poly.Core.CandidateReducibleSubst
import FX1Poly.Core.SemanticTypeDomain
import FX1Poly.Core.WhnfInterpretation
import FX1Poly.Core.WhnfInterpretationDeterminism
import FX1Poly.Core.WhnfInterpretationHeadExpansion
import FX1Poly.Core.WhnfInterpretationHeadReduce
import FX1Poly.Core.WhnfInterpretationRename
import FX1Poly.Core.ReducibleType
import FX1Poly.Core.ReducibleTypeHeadExpansion
import FX1Poly.Core.ReducibleTypeArrowCandidate
import FX1Poly.Core.ReducibleTypeAbstraction
import FX1Poly.Core.ReducibleTypeClosedUnderStep
import FX1Poly.Core.ReducibleTypeInversion
import FX1Poly.Core.PolygraphConvergentDecision
import FX1Poly.Core.SconingWitness
import FX1Poly.Core.StrongNormalizationRename
import FX1Poly.Core.StrongNormalizationRenameForward
import FX1Poly.Core.StrongNormalizationSmokeCorpus
import FX1Poly.Core.StrongNormalizationFormerCorpus
import FX1Poly.Core.StrongNormalizationBetaEtaLeaves
import FX1Poly.Core.StrongNormalizationBetaEtaFormers
import FX1Poly.Core.StrongNormalizationApplication
import FX1Poly.Core.StrongNormalizationEta
import FX1Poly.Core.StepBetaEtaConfluence
import FX1Poly.Core.StepIotaEtaDoubleStrips

/-! # FX1PolyAudit/AuditCoreSubstrate — namespace zero-axiom sweep

Persistent zero-axiom gate for the foundational term-substrate slice:

* Generator substrate: `GeneratorCore` / `GeneratorMetadata` /
  `GeneratorAdmission` / `GenPayloadEvidence` / `GeneratorTotalityClass` /
  `GeneratorChildSpecsDim0` / `CoreFxProfile`.
* Cell-shape vocabulary: `RuleSpec` / `CheckResult` /
  `ConsistencyStrength` / `SiteOpenness` /
  `HasEqualDim`.
* `RawTerm` + the full rename/subst commute ladder
  (`RawTermSubstDefs` / `GenAlgebra` / `Fold` / `LiftsRaw` /
  `RawTermRename*` / `RawTermSubst*` / `RawTermStrengthen` / …).
* `RawCell` + `RawSize` / `RawCellDecEq` / `RawCellCode` /
  `RawCellRenameSubst` / `RawCellCascadeLaws`.
* Reduction leaves: `Step` / `StepStar` / `StepInversion` / `StepEta`.

The `#audit_namespace` sweep walks EVERY loaded declaration under the
namespace and fails the build at the first axiom leak — so this single
gate auto-covers every Core declaration without a hand-maintained
per-decl list.  It also re-checks the native infra under
`FX1Poly.Foundation`.
-/

#audit_namespace FX1Poly.Core
#audit_namespace FX1Poly.Foundation

-- Forward strong-normalization preservation along a left-invertible renaming: the neutral-leaf
-- ingredient of the stratified reducibility rename-closure.  Explicit per-decl gate.
#assert_no_axioms FX1Poly.Core.StepStar.isStronglyNormalizing_rename_of_leftInverse

-- The complete weak-head reduction commutes with renaming (the renaming twin of WeakHeadStep.subst):
-- the whnfExpand-arm ingredient of the stratified ReducibleTypeStep rename-closure.
#assert_no_axioms FX1Poly.Core.IotaHeadStep.rename
#assert_no_axioms FX1Poly.Core.WeakHeadStep.rename

-- A left-invertible renaming REFLECTS weak-head reduction (hence preserves weak-head normality): the
-- neutral-arm ingredient of the stratified ReducibleTypeStep rename-closure, derived from WeakHeadStep.rename
-- preservation run on the left inverse plus the round-trip (no per-shape inversion grind).
#assert_no_axioms FX1Poly.Core.RawTerm.rename_leftInverse_roundTrip
#assert_no_axioms FX1Poly.Core.WeakHeadStep.rename_reflects_of_leftInverse
#assert_no_axioms FX1Poly.Core.WeakHeadStep.rename_preserves_weakHeadNormal_of_leftInverse

-- Pull a full `Step` (not just weak-head) back along an injective renaming: the confinement-free half of
-- full rename-reflection-with-image.  The left-inverse property holds at every index, so the round-trip
-- rename-inverse-after-rename = id collapses definitionally; Step.rename (forward) transports the step.
#assert_no_axioms FX1Poly.Core.Step.renamePullbackOfLeftInverse
#assert_no_axioms FX1Poly.Core.Step.renameReflectsExistsOfLeftInverse
#assert_no_axioms FX1Poly.Core.StepStar.renamePullbackOfLeftInverse
-- Generic head-recovery for a renamed cell (RawTerm.rename_eq_mkGen): rename rho term = mkGen gen _ _ implies
-- term = mkGen gen _ _.  The generator-generic head-recovery half of rename_eq_app/lam; the uniform first step
-- of every arm of full arbitrary-renaming Step reflection, a per-eliminator induction (the injective
-- renamePullback above does not serve the all-renamings Kripke-arrow CR3 closure).
#assert_no_axioms FX1Poly.Core.RawTerm.rename_eq_mkGen
-- The beta arm of arbitrary-rho Step reflection (Step.reflectBeta): rename rho term = app (lam renamedBody)
-- renamedArg implies there is t' with Step term t' and rename rho t' = subst0 renamedBody renamedArg.  Recovers
-- the source beta-redex via rename_eq_app/rename_eq_lam, beta-reduces, and aligns the contractum image by
-- rename_subst0_commute.  The substitution leaf arm of full reflection; a standalone base case.
#assert_no_axioms FX1Poly.Core.Step.reflectBeta
-- The boolElim child-projection iota arms of arbitrary-rho Step reflection (Step.reflectIotaBoolTrue/BoolFalse):
-- rename rho term = boolElim (boolTrue/boolFalse) then else implies there is t' with Step term t' and
-- rename rho t' = then/else.  Head recovery (rename_eq_mkGen) + concrete gen_boolElim rfl-distribution +
-- injection + gen_boolTrue/boolFalse scrutinee recovery; the contractum is a child (no subst).
#assert_no_axioms FX1Poly.Core.Step.reflectIotaBoolTrue
#assert_no_axioms FX1Poly.Core.Step.reflectIotaBoolFalse
-- The pair-projection iota arms of arbitrary-rho Step reflection (Step.reflectIotaFstPair/SndPair):
-- rename rho term = fst/snd (pair first second) implies there is t' with Step term t' and
-- rename rho t' = first/second.  Two-level recovery: gen_fst/gen_snd head (rename_eq_mkGen) + concrete
-- rfl-distribution + injection, then gen_pair scrutinee recovery; the projected child is the contractum.
#assert_no_axioms FX1Poly.Core.Step.reflectIotaFstPair
#assert_no_axioms FX1Poly.Core.Step.reflectIotaSndPair

-- The neutral leaf of the stratified ReducibleTypeStep rename-closure (type + member level): the structural
-- fragment, separate from the Kripke-indexed piType arm (see the StratifiedReducibleTypeRename docstring).
#assert_no_axioms FX1Poly.Core.ReducibleTypeStep.neutralRename_of_leftInverse
#assert_no_axioms FX1Poly.Core.ReducibleTypeStep.neutralRenameMember_of_leftInverse

-- Concrete strong-normalization smoke corpus (variable leaf, unit leaf, identity beta-redex).
#assert_no_axioms FX1Poly.Core.smoke_variable_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_unit_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_identityRedex_isStronglyNormalizing

-- genFormationPi codomain-SN extraction: the relation-agnostic pure-SN binder reconciliation, the
-- substitution-algebra core of openBodyOfConsSubstMember.  SN of the lifted-substitution body from SN of its
-- cons-instantiation (binder-split keystone + ofSubst0Body); it mentions no reducibility relation, so the fuel
-- (IsReducibleMemberAt) and denote (IsReducibleMemberAtDenote) routes both reduce the codomain-under-binder
-- SN obligation to this one fact once their CR1 supplies the member's SN.
#assert_no_axioms FX1Poly.Core.IsStronglyNormalizing.openBodyOfConsSubst

-- One closed strong-normalization witness per raw former family, plus two nested compositional witnesses
-- (closures compose with correct de Bruijn scope threading through the under-binder slots).  Each exercises
-- one Step.from_<former> congruence injection on a concrete cell.
#assert_no_axioms FX1Poly.Core.smoke_lam_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_pathLam_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_diffLambda_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_natSucc_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_optionSome_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_eitherInl_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_eitherInr_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_refl_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_modIntro_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_pair_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_listCons_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_glueIntro_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_arrowCode_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_productCode_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_sumCode_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_eitherCode_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_equivCode_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_piTyCode_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_sigmaTyCode_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_polyFunctor_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_nestedLamNatSucc_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_nestedPiSigma_isStronglyNormalizing
-- Modal core + universe-mode bridge family (congruence-only operators): one closed SN witness per
-- operator, so a regression in any single congruence closure fails its own gated witness.
#assert_no_axioms FX1Poly.Core.smoke_modElim_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_subsume_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_liftInnerToOuter_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_lowerOuterToInner_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.smoke_modElimLiftInnerToOuter_isStronglyNormalizing

-- The type-code-former family inhabits its neutral universe as a reducible member (the conv-complete
-- IsReducibleMember layer the fundamental theorem assembles over).  atNeutralClassifier is the
-- characterization (membership at a neutral classifier = strong normalization); the seven formers
-- (dependent pi/sigma + non-dependent arrow/product/sum/either/equiv) discharge via their SN closures.
#assert_no_axioms FX1Poly.Core.IsReducibleMember.atNeutralClassifier
#assert_no_axioms FX1Poly.Core.IsReducibleMember.piFormerInNeutralUniverse
#assert_no_axioms FX1Poly.Core.IsReducibleMember.sigmaFormerInNeutralUniverse
#assert_no_axioms FX1Poly.Core.IsReducibleMember.arrowFormerInNeutralUniverse
#assert_no_axioms FX1Poly.Core.IsReducibleMember.productFormerInNeutralUniverse
#assert_no_axioms FX1Poly.Core.IsReducibleMember.sumFormerInNeutralUniverse
#assert_no_axioms FX1Poly.Core.IsReducibleMember.eitherFormerInNeutralUniverse
#assert_no_axioms FX1Poly.Core.IsReducibleMember.equivFormerInNeutralUniverse

-- The SN entry points (variable / unit leaves) are robust under the eta extension
-- (Step.betaEta = Step union Step.eta).  Leaf eta-inversion + the reusable no-betaEta-step Acc base.
#assert_no_axioms FX1Poly.Core.noEtaStep_var
#assert_no_axioms FX1Poly.Core.noEtaStep_unit
#assert_no_axioms FX1Poly.Core.isStronglyNormalizingBetaEta_of_noBetaEtaStep
#assert_no_axioms FX1Poly.Core.var_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.unit_isStronglyNormalizingBetaEta

-- The full per-former corpus is robust under the eta extension.  Two generic StepChildren-normality
-- helpers + one betaEta-SN witness per former (the formers over unit children are betaEta normal: cong has
-- no normal-child StepChildren, and no Step.eta fires by shape mismatch).
#assert_no_axioms FX1Poly.Core.noStepChildren_oneNormalChild
#assert_no_axioms FX1Poly.Core.noStepChildren_twoNormalChildren
#assert_no_axioms FX1Poly.Core.smoke_lam_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_pathLam_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_diffLambda_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_natSucc_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_optionSome_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_eitherInl_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_eitherInr_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_refl_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_modIntro_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_pair_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_listCons_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_glueIntro_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_arrowCode_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_productCode_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_sumCode_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_eitherCode_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_equivCode_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_piTyCode_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_sigmaTyCode_isStronglyNormalizingBetaEta
#assert_no_axioms FX1Poly.Core.smoke_polyFunctor_isStronglyNormalizingBetaEta
-- and the identity beta-redex: the corpus's first non-normal-form (head-expansion) betaEta witness.
#assert_no_axioms FX1Poly.Core.noStep_lamVar0
#assert_no_axioms FX1Poly.Core.smoke_identityRedex_isStronglyNormalizingBetaEta

-- Kripke-indexed candidates make arrow rename-closure definitional.  Non-dependent presheaf
-- functoriality + the arrow rename-closure.
#assert_no_axioms FX1Poly.Core.transport_transport_pointwise
#assert_no_axioms FX1Poly.Core.kripkeArrow_transport_pointwise
-- Dependent Kripke arrow (the Pi case): codomain family transport functoriality + dependent rename-closure.
#assert_no_axioms FX1Poly.Core.codFamily_transport_transport_pointwise
#assert_no_axioms FX1Poly.Core.kripkeArrowDep_transport_pointwise
-- CR1 structural ingredient: an application's strong normalization descends to its function (Acc pullback).
#assert_no_axioms FX1Poly.Core.appFunctionCongStep
#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_of_appFunction_aux
#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_of_appFunction
-- CR1 for the Kripke arrow (non-dependent + dependent): members are strongly normalizing (Tait argument).
#assert_no_axioms FX1Poly.Core.kripkeArrow_stronglyNormalizing
#assert_no_axioms FX1Poly.Core.kripkeArrowDep_stronglyNormalizing
-- CR2 for the Kripke arrow (non-dependent + dependent): forward Step closure.
#assert_no_axioms FX1Poly.Core.kripkeArrow_forwardStep
#assert_no_axioms FX1Poly.Core.kripkeArrowDep_forwardStep
-- CR3 structural ingredient: neutrality is preserved by renaming (needed so the applied fresh-var head
-- `rename furtherRenaming functionTerm` stays neutral in the Kripke arrow's neutral backward closure).
#assert_no_axioms FX1Poly.Core.IsNeutral.rename
-- A neutral term's one-step reduct is again neutral: a neutral can only step by congruence (no root redex
-- fires, the principal child being neutral never a constructor), and congruence preserves the stuck shape.
-- Discharges the `neutralClosedUnderStep` hypothesis of `CanonicalFormsPredicate.closedUnderStep`.
#assert_no_axioms FX1Poly.Core.IsNeutral.closedUnderStep
-- boolElim s t e is strongly normalizing when its scrutinee and both branches are SN (the branch-SN form,
-- via a triple nested accessibility induction absorbing the iota-redex).  The iota-head-expansion SN
-- foundation for boolElim reducibility and the fundamental theorem's eliminator arm.
#assert_no_axioms FX1Poly.Core.StepStar.boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
-- Identity eliminators: idJ / idStrictRec base witness is SN when base and witness are SN, via the
-- boolElim-style double nested accessibility induction over base and witness.
#assert_no_axioms FX1Poly.Core.StepStar.idJ_isStronglyNormalizing_of_strongly_normalizing_base
#assert_no_axioms FX1Poly.Core.StepStar.idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base

-- Generic non-variable cell commutation for fold traversals: the substrate for subst/rename through an
-- abstract formation cell.  fold_mkGen_of_ne_var exposes the fold non-variable branch for an abstract
-- non-gen_var generator (dsimp [fold] + dif_neg); subst/rename_mkGen_of_ne_var are the traversal corollaries
-- (canonical_algebra_eq_mkGen rebuild).  The payload cast is
-- Generator.payload_scope_invariant_of_not_var (the generator enumeration in one place).  The category-C
-- formation-family consumers (HasTypeDescSubstitution/Weakening + grown twins) discharge their pi/sigma
-- cases through it generically, so a new formation row touches none of them.
#assert_no_axioms FX1Poly.Core.fold_mkGen_of_ne_var
#assert_no_axioms FX1Poly.Core.RawTerm.subst_mkGen_of_ne_var
#assert_no_axioms FX1Poly.Core.RawTerm.rename_mkGen_of_ne_var
