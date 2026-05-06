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

namespace LeanFX2.Tools

/-! ## SummaryDebtDashboard — aggregate semantic-debt dashboard. -/

-- AGGREGATE SEMANTIC-DEBT DASHBOARD.  Renders the project's full debt
-- floor in one prominent multi-line banner at end of build.  Reads live
-- from the environment via every per-debt-class record collector.
-- Strictly informational; the per-budget gates above already failed
-- the build if any ratchet rose, so a rendered dashboard means every
-- budget held this build.  Visibility layer: makes today's debt counts
-- and bridge-coverage status surface clearly amid build noise so a
-- reader skimming the build log sees at a glance which classes still
-- have debt and how the ratchets stand.
#audit_debt_dashboard LeanFX2.Term LeanFX2.Ty LeanFX2

end LeanFX2.Tools
