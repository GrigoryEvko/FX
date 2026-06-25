import FX1PolyAudit.Typed.Shards.ChurchTermModel.Part01
import FX1PolyAudit.Typed.Shards.ChurchTermModel.Part02
import FX1PolyAudit.Typed.Shards.ChurchTermModel.Part03
import FX1PolyAudit.Typed.Shards.ChurchTermModel.Part04
import FX1PolyAudit.Typed.Shards.ChurchTermModel.Part05

/-! # FX1PolyAudit/AuditTypedChurchTermModel — thin re-export aggregator

The former monolithic semantic shard, now chunk-split into
`FX1PolyAudit.Typed.Shards.ChurchTermModel.Part01..Part05` so each piece stays under the
per-file eval ceiling and elaborates in parallel.  This module carries no eval of its own;
importing it transitively loads every part, so `AuditTyped`'s coverage is unchanged. -/
