import FX1PolyAudit.Typed.Shards.UnitEtaReadback.Part01
import FX1PolyAudit.Typed.Shards.UnitEtaReadback.Part02
import FX1PolyAudit.Typed.Shards.UnitEtaReadback.Part03
import FX1PolyAudit.Typed.Shards.UnitEtaReadback.Part04
import FX1PolyAudit.Typed.Shards.UnitEtaReadback.Part05
import FX1PolyAudit.Typed.Shards.UnitEtaReadback.Part06

/-! # FX1PolyAudit/AuditTypedUnitEtaReadback — thin re-export aggregator

The former monolithic semantic shard, now chunk-split into
`FX1PolyAudit.Typed.Shards.UnitEtaReadback.Part01..Part06` so each piece stays under the
per-file eval ceiling and elaborates in parallel.  This module carries no eval of its own;
importing it transitively loads every part, so `AuditTyped`'s coverage is unchanged. -/
