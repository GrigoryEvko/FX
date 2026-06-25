import FX1PolyAudit.Typed.Shards.CanonicalForms.Part01
import FX1PolyAudit.Typed.Shards.CanonicalForms.Part02
import FX1PolyAudit.Typed.Shards.CanonicalForms.Part03
import FX1PolyAudit.Typed.Shards.CanonicalForms.Part04

/-! # FX1PolyAudit/AuditTypedCanonicalForms — thin re-export aggregator

The former monolithic semantic shard, now chunk-split into
`FX1PolyAudit.Typed.Shards.CanonicalForms.Part01..Part04` so each piece stays under the
per-file eval ceiling and elaborates in parallel.  This module carries no eval of its own;
importing it transitively loads every part, so `AuditTyped`'s coverage is unchanged. -/
