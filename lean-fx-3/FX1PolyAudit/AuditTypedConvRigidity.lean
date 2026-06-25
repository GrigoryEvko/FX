import FX1PolyAudit.Typed.Shards.ConvRigidity.Part01
import FX1PolyAudit.Typed.Shards.ConvRigidity.Part02
import FX1PolyAudit.Typed.Shards.ConvRigidity.Part03
import FX1PolyAudit.Typed.Shards.ConvRigidity.Part04
import FX1PolyAudit.Typed.Shards.ConvRigidity.Part05

/-! # FX1PolyAudit/AuditTypedConvRigidity — thin re-export aggregator

The former monolithic semantic shard, now chunk-split into
`FX1PolyAudit.Typed.Shards.ConvRigidity.Part01..Part05` so each piece stays under the
per-file eval ceiling and elaborates in parallel.  This module carries no eval of its own;
importing it transitively loads every part, so `AuditTyped`'s coverage is unchanged. -/
