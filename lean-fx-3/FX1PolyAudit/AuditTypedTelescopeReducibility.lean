import FX1PolyAudit.Typed.Metatheory.Reducibility.Telescope.TelescopeReducibility
import FX1PolyAudit.Typed.Metatheory.Reducibility.Telescope.TelescopeReducibilityMore

/-! # FX1PolyAudit/AuditTypedTelescopeReducibility — re-export shim

The telescope-reducibility audit gates were sharded into the mirror-tree files under
`FX1PolyAudit.Typed.Metatheory.Reducibility.Telescope.TelescopeReducibility*` (each under 50
`#assert_no_axioms` evals, elaborating in parallel).  This file re-imports those shards so existing
importers (the `AuditTyped` aggregator) keep resolving the original module name; all gate content and
counts are conserved exactly across the shards. -/
