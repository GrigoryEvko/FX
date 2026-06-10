import FX1PolyAudit.AuditOmegacEConfluence
import FX1PolyAudit.AuditOmegacERewriters

/-! # FX1PolyAudit/AuditOmegacE — aggregator over the granular audit shards

The former AuditOmegacE gate monolith, now the omega-cE word-problem leg: every gate lives in one of
the imported shard files, which elaborate IN PARALLEL (the monolith serialized them)
and re-elaborate individually on incremental gate edits.  Gate content and counts are
conserved exactly; each shard carries the full import block so namespace-sweep
coverage is unchanged. -/
