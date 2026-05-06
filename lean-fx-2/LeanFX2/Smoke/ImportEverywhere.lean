import LeanFX2.Smoke.AuditAll
import LeanFX2.Smoke.AuditNamespace
import LeanFX2.Smoke.ImportSurface
import LeanFX2.Smoke.StrictComposition
import LeanFX2.Tools.StrictHarness
import LeanFX2.Tools.Tactics.Cast
import LeanFX2.Tools.Tactics.HEq
import LeanFX2.Tools.Tactics.SimpStrip

/-! # Smoke/ImportEverywhere

Whole-loaded-cone import census.

`Smoke.ImportSurface` is the policy gate for production imports.  This module
loads the broader smoke/tool cone too, then reuses the global host-heavy
allowlist and import summary so dependency drift in audit-only files is visible
during `lake build LeanFX2`.
-/

namespace LeanFX2.Smoke.ImportEverywhere

#assert_host_heavy_import_surface_allowlisted
#audit_import_surface_summary

end LeanFX2.Smoke.ImportEverywhere
