import FX1PolyAudit.AuditTypedCanonicalForms
import FX1PolyAudit.AuditTypedCellShapeSubstrate
import FX1PolyAudit.AuditTypedCheckerInference
import FX1PolyAudit.AuditTypedChurchTermModel
import FX1PolyAudit.AuditTypedContextConversion
import FX1PolyAudit.AuditTypedConvRigidity
import FX1PolyAudit.AuditTypedDefenseCorpus
import FX1PolyAudit.AuditTypedFundamentalBounded
import FX1PolyAudit.AuditTypedFundamentalDenote
import FX1PolyAudit.AuditTypedFundamentalLeveled
import FX1PolyAudit.AuditTypedGradedDimensions
import FX1PolyAudit.AuditTypedHonestyClassifiers
import FX1PolyAudit.AuditTypedLedgers
import FX1PolyAudit.AuditTypedReducibilityCandidates
import FX1PolyAudit.AuditTypedStrengthenReflection
import FX1PolyAudit.AuditTypedStrongNormalization
import FX1PolyAudit.AuditTypedSubjectReductionEta
import FX1PolyAudit.AuditTypedSubstVecCwR
import FX1PolyAudit.AuditTypedTelescopeReducibility
import FX1PolyAudit.AuditTypedTypingEngines
import FX1PolyAudit.AuditTypedUnitEtaReadback

/-! # FX1PolyAudit/AuditTyped — aggregator over the granular audit shards

The former AuditTyped gate monolith, now the typed layer, semantically sharded: every gate lives in one of
the imported shard files, which elaborate IN PARALLEL (the monolith serialized them)
and re-elaborate individually on incremental gate edits.  Gate content and counts are
conserved exactly; each shard carries the full import block so namespace-sweep
coverage is unchanged. -/
