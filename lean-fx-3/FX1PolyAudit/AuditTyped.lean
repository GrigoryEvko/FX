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
import FX1PolyAudit.AuditGen

/-! # FX1PolyAudit/AuditTyped — aggregator over the granular audit shards

The former AuditTyped gate monolith, now the typed layer, semantically sharded: every gate lives in one of
the imported shard files, which elaborate IN PARALLEL (the monolith serialized them)
and re-elaborate individually on incremental gate edits.  Gate content and counts are
conserved exactly; each shard carries the full import block so namespace-sweep
coverage is unchanged.

## Whole-namespace axiom sweep

Every other major kernel namespace has a `#audit_namespace` sweep (Core/Foundation in
`AuditCoreSubstrateSweeps`, the profile family in `AuditProfile`, `NbE` in `AuditNbE`,
`FXProfile` in `AuditFXProfile`).  `FX1Poly.Typed` — the largest and most
safety-critical namespace (the typed kernel: `HasTypeUnion`, the grown engine, subject
reduction, canonicity, strong normalization, decidable conversion) — had ONLY hand-listed
per-decl gates and no whole-namespace sweep.  The `#audit_namespace FX1Poly.Typed` below
closes that hole: it walks every loaded `FX1Poly.Typed` declaration and fails at the first
axiom leak, so a NEW typed declaration that depends on an axiom is caught even if no one
remembers to add its per-decl gate.  Coverage is the aggregator's transitive import closure
(the same model every namespace sweep uses); the `#assert_namespace_min_count` guard pins
that closure against the silent under-import footgun (HON-16). -/

#audit_namespace FX1Poly.Typed
-- Floor pinned below the ~4467 loaded count: headroom for ordinary lemma consolidation,
-- but a dropped shard (the under-import footgun, hundreds of decls) trips it loudly.
#assert_namespace_min_count FX1Poly.Typed 4400
