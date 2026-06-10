import FX1PolyAudit.AuditCoreSubstrateEta
import FX1PolyAudit.AuditCoreSubstrateSweeps

/-! # FX1PolyAudit/AuditCoreSubstrate — aggregator over the granular audit shards

The former AuditCoreSubstrate gate monolith, now the Core/Foundation namespace sweeps: every gate lives in one of
the imported shard files, which elaborate IN PARALLEL (the monolith serialized them)
and re-elaborate individually on incremental gate edits.  Gate content and counts are
conserved exactly; each shard carries the full import block so namespace-sweep
coverage is unchanged. -/
