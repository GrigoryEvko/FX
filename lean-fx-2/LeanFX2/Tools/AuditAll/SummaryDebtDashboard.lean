import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1.LeanKernel.Name
import LeanFX2.FX1.LeanKernel.Level
import LeanFX2.FX1.LeanKernel.Expr
import LeanFX2.FX1.LeanKernel.Substitution
import LeanFX2.FX1.LeanKernel.Reduction
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1
import LeanFX2.FX1Bridge
-- Gate files whose elabs populate the audit-count env extension.
-- The dashboard reads these counts via `lookupAuditCountOrZero` instead
-- of recomputing.  Importing the gate files ensures Lean merges their
-- env-extension state into this file's environment before the
-- `#audit_debt_dashboard` command fires.
import LeanFX2.Tools.AuditAll.GatesAxiomAdj
import LeanFX2.Tools.AuditAll.GatesBroad
import LeanFX2.Tools.AuditAll.GatesCore
import LeanFX2.Tools.AuditAll.GatesEffect
import LeanFX2.Tools.AuditAll.GatesNaming
import LeanFX2.Tools.AuditAll.GatesNumOps
import LeanFX2.Tools.AuditAll.GatesShape

namespace LeanFX2.Tools

/-! ## SummaryDebtDashboard — aggregate semantic-debt dashboard. -/

-- AGGREGATE SEMANTIC-DEBT DASHBOARD.  Renders the project's full debt
-- floor in one prominent multi-line banner at end of build.  Reads
-- audit-count cache populated by the budget gates above.  Strictly
-- informational; the per-budget gates already failed the build if any
-- ratchet rose, so a rendered dashboard means every budget held this
-- build.  Visibility layer: makes today's debt counts and
-- bridge-coverage status surface clearly amid build noise so a reader
-- skimming the build log sees at a glance which classes still have
-- debt and how the ratchets stand.
#audit_debt_dashboard LeanFX2.Term LeanFX2.Ty LeanFX2

end LeanFX2.Tools
