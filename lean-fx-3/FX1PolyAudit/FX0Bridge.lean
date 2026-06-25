import FX1PolyAudit.FX0.FX0Bridge

/-! # FX1PolyAudit/FX0Bridge — thin re-export shim pending removal.

This module's content moved to `FX1PolyAudit.FX0.FX0Bridge` during the audit-directory
restructure (cross-cutting corpus/FX0/ledger cluster out of the root).
This shim re-exports it so importers naming `import FX1PolyAudit.FX0Bridge`
keep resolving until the orchestrator repoints them and removes the shim. -/
