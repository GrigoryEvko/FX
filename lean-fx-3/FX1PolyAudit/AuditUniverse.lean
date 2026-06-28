import FX1PolyAudit.Tier0.Type.Level.LevelExpr
import FX1PolyAudit.Tier0.Type.Level.LevelExprImpredicativeClosure
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify01
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify02
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify03
import FX1PolyAudit.Tier0.Type.Universe.UniverseFlag
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify04
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify05
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify06
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify07
import FX1PolyAudit.Tier0.Type.Level.LevelExprSerialize
import FX1PolyAudit.Core.Rewriting.Normalize.NbE.LevelExprComplexity
import FX1PolyAudit.Tier0.Type.Universe.UniverseFlagSerialize
import FX1PolyAudit.Tier0.Type.Universe.UniverseFlagStrength
import FX1PolyAudit.Tier0.Type.Universe.UniversePayloadSerialize

/-! # FX1PolyAudit/AuditUniverse — aggregator over the granular audit shards

The former AuditUniverse gate monolith, now the LevelExpr/UniverseFlag layer: every gate lives in one of
the imported shard files, which elaborate IN PARALLEL (the monolith serialized them)
and re-elaborate individually on incremental gate edits.  Gate content and counts are
conserved exactly; each shard carries the full import block so namespace-sweep
coverage is unchanged. -/
