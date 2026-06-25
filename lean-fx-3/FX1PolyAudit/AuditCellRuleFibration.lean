import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.Tier0.RuleFibration
import FX1PolyAudit.Typed.CellRuleFibration

/-! # FX1PolyAudit/AuditCellRuleFibration — re-export shim
The cell-rule-fibration zero-axiom gates this flat file once held now live in the
source-mirroring tree: the Tier0 substrate gate under
`FX1PolyAudit/Tier0/RuleFibration.lean` and the Typed instance + per-generator
smokes under `FX1PolyAudit/Typed/CellRuleFibration.lean`; this file re-exports
both so existing importers keep resolving every gate. -/
