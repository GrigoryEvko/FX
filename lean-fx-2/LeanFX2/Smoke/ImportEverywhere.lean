import LeanFX2.Smoke.AuditAll
import LeanFX2.Smoke.AuditNamespace
import LeanFX2.Smoke.ImportSurface
import LeanFX2.Smoke.StrictComposition
import LeanFX2.Tools.StrictHarness
import LeanFX2.Tools.Tactics.Cast
import LeanFX2.Tools.Tactics.HEq
import LeanFX2.Tools.Tactics.SimpStrip
import LeanFX2.Lean.Kernel.Audit
import LeanFX2.Lean.Kernel.Check
import LeanFX2.Lean.Kernel.HasType
import LeanFX2.Lean.Kernel.Inductive
import LeanFX2.Lean.Kernel.Soundness
import LeanFX2.Sketch.Wave9

/-! # Smoke/ImportEverywhere

Whole-loaded-cone import census.

`Smoke.ImportSurface` is the policy gate for production imports.  This module
loads the broader smoke/tool cone, the legacy Lean-kernel scaffold stubs, and
the standalone sketch cone too, then reuses the global host-heavy allowlist and
import summary so dependency drift in audit-only or non-production files is
visible during `lake build LeanFX2`.
-/

namespace LeanFX2.Smoke.ImportEverywhere

#assert_host_heavy_import_surface_allowlisted
#assert_legacy_lean_kernel_import_surface_clean
#audit_import_surface_summary

end LeanFX2.Smoke.ImportEverywhere
