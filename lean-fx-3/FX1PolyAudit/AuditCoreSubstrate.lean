import FX1PolyAudit.AuditGen
-- Sink files of the foundational term-substrate slice (importing these
-- transitively loads every migrated FX1Poly.Core declaration).
import FX1Poly.Core.AbstractTermSpine
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
import FX1Poly.Core.RuleSpec
import FX1Poly.Core.SiteOpenness
import FX1Poly.Core.SpikeDimTransport
import FX1Poly.Core.StepEta
import FX1Poly.Core.StepInversion
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
import FX1Poly.Core.StepEtaEtaCriticalPairs
import FX1Poly.Core.StepIotaEtaInsideBinder
import FX1Poly.Core.StepBetaEtaPreservesShape
import FX1Poly.Core.SubjectReductionEtaBinder
import FX1Poly.Core.IdEliminatorLayer
-- Strong normalization (leaves/neutral/constructors/redexes/eta) + beta-eta
-- confluence + iota-eta double strips + concrete neutral predicate.
import FX1Poly.Core.NeutralTerm
import FX1Poly.Core.ReducibilityCandidate
import FX1Poly.Core.StrongNormalizationRedexes
import FX1Poly.Core.StrongNormalizationIotaRedexes
import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationEta
import FX1Poly.Core.StepBetaEtaConfluence
import FX1Poly.Core.StepIotaEtaDoubleStrips

/-! # FX1PolyAudit/AuditCoreSubstrate — namespace zero-axiom sweep

Persistent zero-axiom gate for the foundational term-substrate slice
migrated out of lean-fx-2's `Foundation/PolyCell/Core`:

* Generator substrate: `GeneratorCore` / `GeneratorMetadata` /
  `GeneratorAdmission` / `GenPayloadEvidence` / `GeneratorTotalityClass` /
  `GeneratorChildSpecsDim0` / `AbstractTermSpine` / `CoreFxProfile`.
* Cell-shape vocabulary: `RuleSpec` / `CheckResult` /
  `ConsistencyStrength` / `SiteOpenness` / `SpikeDimTransport` /
  `HasEqualDim`.
* `RawTerm` + the full rename/subst commute ladder
  (`RawTermSubstDefs` / `GenAlgebra` / `Fold` / `LiftsRaw` /
  `RawTermRename*` / `RawTermSubst*` / `RawTermStrengthen` / …).
* `RawCell` + `RawSize` / `RawCellDecEq` / `RawCellCode` /
  `RawCellRenameSubst` / `RawCellCascadeLaws`.
* Reduction leaves: `Step` / `StepStar` / `StepInversion` / `StepEta`.

The `#audit_namespace` sweep walks EVERY loaded declaration under the
namespace and fails the build at the first axiom leak — so this single
gate auto-covers all ~430 migrated declarations and every future Core
slice without a hand-maintained per-decl list.  It also re-checks the
native infra under `FX1Poly.Foundation`.
-/

#audit_namespace FX1Poly.Core
#audit_namespace FX1Poly.Foundation
