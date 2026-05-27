import LeanFX2.Smoke.AuditAll
import LeanFX2.Smoke.AuditTacticsCast
import LeanFX2.Smoke.AuditTacticsChoreography
import LeanFX2.Smoke.AuditTacticsSN
import LeanFX2.Smoke.AuditTacticsSimpStrip
import LeanFX2.Smoke.AuditTacticsStrengthen
import LeanFX2.Smoke.StrictComposition
import LeanFX2.Tools.StrictHarness
import LeanFX2.Tools.Tactics.Cast
import LeanFX2.Tools.Tactics.Chains
import LeanFX2.Tools.Tactics.Choreography
import LeanFX2.Tools.Tactics.HEq
import LeanFX2.Tools.Tactics.RawInversion
import LeanFX2.Tools.Tactics.SN
import LeanFX2.Tools.Tactics.SimpStrip
import LeanFX2.Tools.Tactics.Strengthen
import LeanFX2.Surface.HostLex
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.Sketch.Wave9

/-! # Smoke/ImportEverywhere

Whole-loaded-cone import census.

`Smoke.ImportSurface` is the policy gate for production imports.  This module
loads the broader smoke/tool cone, the FX1 Lean-kernel model, and the standalone
sketch cone too, then reuses the global host-heavy allowlist and import summary
so dependency drift in audit-only or non-production files is visible during
`lake build LeanFX2`.
-/

namespace LeanFX2.Smoke.ImportEverywhere

#assert_host_heavy_import_surface_allowlisted
#assert_public_umbrella_imports_isolated
#assert_host_boundary_isolated
#assert_legacy_lean_kernel_import_surface_clean
-- `#assert_public_production_umbrella_reaches_all` parked pending
-- POLYCELL: its defining macro in
-- `Tools/StrictHarness/Common/ImportSurface/Layering.lean` is
-- inside a `/- TODO POLYCELL: original body preserved as block
-- comment -/` block (line 11→482), so the macro is unbound.
-- Restore when the layering census body is rewritten against the
-- v2 substrate.
-- #assert_public_production_umbrella_reaches_all
#audit_import_family_summary
#audit_import_surface_summary

end LeanFX2.Smoke.ImportEverywhere
