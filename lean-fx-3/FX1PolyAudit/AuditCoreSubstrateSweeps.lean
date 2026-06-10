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
import FX1Poly.Core.StepRenameReflectEliminatorIota
import FX1Poly.Core.StepRenameReflectAssembly
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
import FX1Poly.Core.StepBetaEtaJoinableConfluence
import FX1Poly.Core.NederpeltNonJoinability
import FX1Poly.Core.GeneratorCountPin
import FX1Poly.Core.StepIotaEtaDoubleStrips

/-! # FX1PolyAudit/AuditCoreSubstrateSweeps — foundational term-substrate zero-axiom gates, shard 1 of 2
(split from the AuditCoreSubstrate monolith for parallel gate elaboration; the full import block is preserved verbatim so the `#audit_namespace` sweeps see every loaded Core/Foundation declaration and the per-decl `#assert_no_axioms` gates resolve). -/

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
-- The base-case ELIMINATOR child-projection iota arms of arbitrary-rho Step reflection (KRIPKE-REFLECT-ELIM,
-- StepRenameReflectEliminatorIota.lean): natElim/natRec on natZero, listElim on listNil, optionMatch on optionNone
-- each eliminate a NULLARY value and project the matching branch. rename rho term = elim (nullaryValue) b1 b2
-- implies there is t' with Step term t' and rename rho t' = b1 (the projected branch). Structurally identical to
-- reflectIotaBoolTrue: gen-elim head recovery (rename_eq_mkGen) + concrete rfl-distribution + injection + nullary
-- scrutinee recovery + the matching Step.iota constructor. Advances the full Step rename-reflection toward
-- Kripke-arrow CR3 (KripkeCandidateRenameClosure.lean), the renaming dimension of the dependent-arrow reducibility
-- candidate the open-context (Kripke) logical relation needs.
#assert_no_axioms FX1Poly.Core.Step.reflectIotaNatElimZero
#assert_no_axioms FX1Poly.Core.Step.reflectIotaNatRecZero
#assert_no_axioms FX1Poly.Core.Step.reflectIotaListElimNil
#assert_no_axioms FX1Poly.Core.Step.reflectIotaOptionMatchNone
-- The app-chain (step-case) ELIMINATOR iota arms (KRIPKE-REFLECT-APPCHAIN): optionMatch on optionSome, eitherMatch
-- on eitherInl/eitherInr match a UNARY value and reduce to the branch APPLIED to the wrapped value
-- (optionMatch (optionSome v) n s ↝ app s v). rename rho term = elim (unaryValue renamedV) b1 b2 implies there is
-- t' with Step term t' and rename rho t' = app renamedBranch renamedV. The contractum is a constructed app cell, so
-- the image eq closes by rename-over-app rfl-distribution + the recovered branch/value renamings; the unary scrutinee
-- needs a TWO-level injection (the optionSome/eitherInl/eitherInr mkGen then its childCons) to expose the value.
#assert_no_axioms FX1Poly.Core.Step.reflectIotaOptionMatchSome
#assert_no_axioms FX1Poly.Core.Step.reflectIotaEitherMatchInl
#assert_no_axioms FX1Poly.Core.Step.reflectIotaEitherMatchInr
-- The identity-eliminator (idJ/idStrictRec on refl) + recursive Nat-recursor (natElim/natRec on natSucc) iota arms
-- (KRIPKE-REFLECT-IDREC). Identity: idJ/idStrictRec project the base-case branch past the refl scrutinee (contractum
-- at child-0, refl value at child-1). Recursive Nat: natElim/natRec on natSucc build a nested app-chain containing a
-- RECURSIVE call on the predecessor (natElim (natSucc p) z s ↝ app (app s p) (natElim p z s)); the deep
-- rename-over-(app/app/elim) image collapses to rfl after substituting the recovered predecessor/zero/succ
-- renamings.
#assert_no_axioms FX1Poly.Core.Step.reflectIotaIdJRefl
#assert_no_axioms FX1Poly.Core.Step.reflectIotaIdStrictRecRefl
#assert_no_axioms FX1Poly.Core.Step.reflectIotaNatElimSucc
#assert_no_axioms FX1Poly.Core.Step.reflectIotaNatRecSucc
-- The deepest redex-leaf arm (KRIPKE-REFLECT-LISTCONS): listElim on listCons. listElim (listCons h t) n c ↝
-- app (app (app c h) t) (listElim t n c) — a TRIPLE-curried application of the cons-branch to head, tail, and a
-- RECURSIVE listElim over the tail. The listCons scrutinee is BINARY (head + tail), so a two-level injection
-- recovers both; substituting the four recovered renamings (head/tail/nil-branch/cons-branch) collapses the
-- deep rename-over-(app/app/app/listElim) image to rfl. This COMPLETES every redex-leaf arm of arbitrary-rho
-- Step reflection-with-image; the ONLY remaining arm is the recursive cong arm (general congruence — needs the
-- sub-reflection IH — the substantive last piece).
#assert_no_axioms FX1Poly.Core.Step.reflectIotaListElimCons
-- THE FULL ASSEMBLY (StepRenameReflectAssembly.lean): the complete arbitrary-renaming Step
-- reflection-with-image Step (rename rho t) u → ∃ t', Step t t' ∧ rename rho t' = u, built as the
-- Step.rec mutual recursion (the Step.subst template run backward). The 18 redex-leaf cases delegate to
-- the shipped reflect arms above; the recursive cong/here/there cases thread the lifted renaming
-- (iterateLiftRaw) through the children spine. This is the Kripke-arrow-CR3 ingredient the open-context
-- (Kripke) logical relation needs to discharge GrownCtxConv-5 (#842), the grown context-conversion piElim crux.
#assert_no_axioms FX1Poly.Core.Step.reflectRename

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

