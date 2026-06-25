import FX1PolyAudit.Typed.Shards.SubjectReductionEta.Part01
import FX1PolyAudit.Typed.Shards.SubjectReductionEta.Part02

/-! # FX1PolyAudit/AuditTypedSubjectReductionEta — thin re-export aggregator

The former monolithic semantic shard, now chunk-split into
`FX1PolyAudit.Typed.Shards.SubjectReductionEta.Part01..Part02` so each piece stays under the
per-file eval ceiling and elaborates in parallel.  This module carries no eval of its own;
importing it transitively loads every part, so `AuditTyped`'s coverage is unchanged. -/
