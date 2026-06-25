import FX1PolyAudit.Typed.Metatheory.Reducibility.Fundamental.FundamentalLeveled
import FX1PolyAudit.Typed.Metatheory.Reducibility.Fundamental.FundamentalLeveledMore
import FX1PolyAudit.Typed.Metatheory.Reducibility.Fundamental.FundamentalLeveledMore2
import FX1PolyAudit.Typed.Metatheory.Reducibility.Fundamental.FundamentalLeveledMore3
import FX1PolyAudit.Typed.Metatheory.Reducibility.Fundamental.FundamentalLeveledMore4
import FX1PolyAudit.Typed.Metatheory.Reducibility.Fundamental.FundamentalLeveledMore5

/-! # FX1PolyAudit/AuditTypedFundamentalLeveled — re-export shim

The level-indexed fundamental-theorem audit gates were sharded into the mirror-tree files under
`FX1PolyAudit.Typed.Metatheory.Reducibility.Fundamental.FundamentalLeveled*` (each under 50
`#assert_no_axioms` evals, elaborating in parallel).  This file re-imports those shards so existing
importers (the `AuditTyped` aggregator) keep resolving the original module name; all gate content and
counts are conserved exactly across the shards. -/
