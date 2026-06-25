import FX1PolyAudit.Typed.Shards.StrengthenReflection.Part01
import FX1PolyAudit.Typed.Shards.StrengthenReflection.Part02

/-! # FX1PolyAudit/AuditTypedStrengthenReflection — thin re-export aggregator

The former monolithic semantic shard, now chunk-split into
`FX1PolyAudit.Typed.Shards.StrengthenReflection.Part01..Part02` so each piece stays under the
per-file eval ceiling and elaborates in parallel.  This module carries no eval of its own;
importing it transitively loads every part, so `AuditTyped`'s coverage is unchanged. -/
