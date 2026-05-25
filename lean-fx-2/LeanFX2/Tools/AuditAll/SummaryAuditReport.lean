import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools

/-! ## SummaryAuditReport — end-of-build audit summary. -/

-- End-of-build summary.  Logs `Total / Clean / Failed` plus per-decl
-- failure list.  Strictly informational (does not throw); the actual
-- blocking happens via `#audit_namespace_strict` above.  Surfaces
-- audit health amid hundreds of OK info lines.
-- TODO POLYCELL: disabled honestly.  The command body is currently
-- preserved only inside `StrictHarness/Reporting.lean`'s disabled
-- cascade-era block; re-enable once Reporting is rebuilt for the
-- PolyCell audit profile.
-- #audit_summary LeanFX2

end LeanFX2.Tools
