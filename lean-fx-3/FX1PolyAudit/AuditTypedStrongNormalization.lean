import FX1PolyAudit.Typed.Metatheory.Reducibility.StrongNormalization
import FX1PolyAudit.Typed.Metatheory.Reducibility.StrongNormalizationMore
import FX1PolyAudit.Typed.Metatheory.Reducibility.StrongNormalizationMore2
import FX1PolyAudit.Typed.Metatheory.Reducibility.StrongNormalizationMore3

/-! # FX1PolyAudit/AuditTypedStrongNormalization — re-export shim

The typed strong-normalization audit gates were sharded into the mirror-tree files under
`FX1PolyAudit.Typed.Metatheory.Reducibility.StrongNormalization*` (each under 50 `#assert_no_axioms`
evals, elaborating in parallel).  This file re-imports those shards so existing importers (the
`AuditTyped` aggregator) keep resolving the original module name; all gate content and counts are
conserved exactly across the shards. -/
