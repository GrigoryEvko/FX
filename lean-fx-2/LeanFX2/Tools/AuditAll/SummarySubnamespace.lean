import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools

/-! ## SummarySubnamespace — per-namespace decl-count snapshot. -/

-- Per-namespace decl-count snapshot.  Strictly informational; surfaces
-- the count distribution across `LeanFX2.*` sub-namespaces so a
-- coverage regression (whole sub-namespace shrinking unexpectedly)
-- is visible at a glance.
-- TODO POLYCELL: disabled honestly.  The command body is currently
-- preserved only inside `StrictHarness/Reporting.lean`'s disabled
-- cascade-era block; re-enable once Reporting is rebuilt for the
-- PolyCell audit profile.
-- #audit_subnamespace_counts

end LeanFX2.Tools
