import FX1PolyAudit.Typed.Metatheory.Denote.FundamentalDenote
import FX1PolyAudit.Typed.Metatheory.Denote.FundamentalDenoteMore
import FX1PolyAudit.Typed.Metatheory.Denote.FundamentalDenoteMore2

/-! # FX1PolyAudit/AuditTypedFundamentalDenote — re-export shim

The denote-keyed fundamental-theorem audit gates were sharded into the mirror-tree files under
`FX1PolyAudit.Typed.Metatheory.Denote.FundamentalDenote*` (each under 50 `#assert_no_axioms` evals,
elaborating in parallel).  This file re-imports those shards so existing importers (the `AuditTyped`
aggregator) keep resolving the original module name; all gate content and counts are conserved exactly
across the shards. -/
