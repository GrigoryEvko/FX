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
import FX1Poly.Core.StrongNormalizationRedexes
import FX1Poly.Core.StrongNormalizationIotaRedexes
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

-- SN-040 (WIP): forward strong-normalization preservation along a left-invertible renaming — the forward
-- direction StrongNormalizationRename.lean explicitly leaves unproven, the neutral-leaf ingredient of the
-- stratified reducibility rename-closure.  Explicit per-decl gate (preferred over sweep-only coverage).
#assert_no_axioms FX1Poly.Core.StepStar.isStronglyNormalizing_rename_of_leftInverse

-- SN-040 (WIP): the complete weak-head reduction commutes with renaming (the renaming twin of
-- WeakHeadStep.subst) — the whnfExpand-arm ingredient of the stratified ReducibleTypeStep rename-closure.
#assert_no_axioms FX1Poly.Core.IotaHeadStep.rename
#assert_no_axioms FX1Poly.Core.WeakHeadStep.rename

-- SN-040 (WIP): a left-invertible renaming REFLECTS weak-head reduction (hence preserves weak-head
-- normality) — the neutral-arm ingredient of the stratified ReducibleTypeStep rename-closure, derived from
-- WeakHeadStep.rename preservation run on the left inverse + the round-trip (no per-shape inversion grind).
#assert_no_axioms FX1Poly.Core.RawTerm.rename_leftInverse_roundTrip
#assert_no_axioms FX1Poly.Core.WeakHeadStep.rename_reflects_of_leftInverse
#assert_no_axioms FX1Poly.Core.WeakHeadStep.rename_preserves_weakHeadNormal_of_leftInverse

-- SN-040 (WIP): the neutral LEAF of the stratified ReducibleTypeStep rename-closure (type + member level).
-- The piType arm is genuinely Kripke-obstructed (see StratifiedReducibleTypeRename docstring); this is the
-- cleanly-shippable structural fragment, off the FT critical path.
#assert_no_axioms FX1Poly.Core.ReducibleTypeStep.neutralRename_of_leftInverse
#assert_no_axioms FX1Poly.Core.ReducibleTypeStep.neutralRenameMember_of_leftInverse
