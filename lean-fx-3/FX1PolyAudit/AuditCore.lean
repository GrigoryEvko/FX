import FX1PolyAudit.AuditCoreCellsAndIota
import FX1PolyAudit.AuditCoreTerminationOrders
import FX1PolyAudit.AuditCoreUniverseMembership

/-! # FX1PolyAudit/AuditCore — aggregator over the granular audit shards

The former AuditCore gate monolith, now the core cell-calculus spine: every gate lives in one of
the imported shard files, which elaborate IN PARALLEL (the monolith serialized them)
and re-elaborate individually on incremental gate edits.  Gate content and counts are
conserved exactly; each shard carries the full import block so namespace-sweep
coverage is unchanged. -/
