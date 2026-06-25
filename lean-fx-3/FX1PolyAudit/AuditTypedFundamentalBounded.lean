import FX1PolyAudit.Typed.Metatheory.Reducibility.Bounded.FundamentalBounded
import FX1PolyAudit.Typed.Metatheory.Reducibility.Bounded.FundamentalBoundedMore
import FX1PolyAudit.Typed.Metatheory.Reducibility.Bounded.FundamentalBoundedMore2
import FX1PolyAudit.Typed.Metatheory.Reducibility.Bounded.FundamentalBoundedMore3
import FX1PolyAudit.Typed.Metatheory.Reducibility.Bounded.FundamentalBoundedMore4
import FX1PolyAudit.Typed.Metatheory.Reducibility.Bounded.FundamentalBoundedMore5

/-! # FX1PolyAudit/AuditTypedFundamentalBounded — re-export shim

The bounded-reducibility fundamental-theorem audit gates (including the genuine `idJ` smoke pins) were
sharded into the mirror-tree files under
`FX1PolyAudit.Typed.Metatheory.Reducibility.Bounded.FundamentalBounded*` (each under 50
`#assert_no_axioms` evals, elaborating in parallel).  This file re-imports those shards so existing
importers (the `AuditTyped` aggregator) keep resolving the original module name; all gate content and
counts are conserved exactly across the shards. -/
