import FX1PolyAudit.AuditFX0PolyBridge
import FX1PolyAudit.AuditFX0PolyCertificates

/-! # FX1PolyAudit/AuditFX0Poly — aggregator over the granular audit shards

The former AuditFX0Poly gate monolith, now the FX0 external-checker layer: every gate lives in one of
the imported shard files, which elaborate IN PARALLEL (the monolith serialized them)
and re-elaborate individually on incremental gate edits.  Gate content and counts are
conserved exactly; each shard carries the full import block so namespace-sweep
coverage is unchanged. -/
