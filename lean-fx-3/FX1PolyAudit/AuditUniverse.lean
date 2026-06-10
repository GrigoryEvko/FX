import FX1PolyAudit.AuditUniverseLevelAlgebra01
import FX1PolyAudit.AuditUniverseLevelAlgebra02
import FX1PolyAudit.AuditUniverseLevelAlgebra03

/-! # FX1PolyAudit/AuditUniverse — aggregator over the granular audit shards

The former AuditUniverse gate monolith, now the LevelExpr/UniverseFlag layer: every gate lives in one of
the imported shard files, which elaborate IN PARALLEL (the monolith serialized them)
and re-elaborate individually on incremental gate edits.  Gate content and counts are
conserved exactly; each shard carries the full import block so namespace-sweep
coverage is unchanged. -/
