import LeanFX2
import LeanFX2.FX1
import LeanFX2.Tools.StrictHarness

/-! # Smoke/ImportSurface — production import-boundary gate.

This smoke imports the rich public umbrella plus the separate FX1 umbrella and
then checks the direct imports of every visible public-production `LeanFX2.*`
module.  Production modules may not depend directly on `Smoke`, `Tools`,
`Sketch`, the broad `LeanFX2` root, or host-heavy modules such as `Lean` and
`Std`; Lean's ambient `Init` prelude is handled by declaration-dependency
audits.  The same broad environment also checks FX1 source imports, prevents
the legacy `LeanFX2.Lean.Kernel` scaffold from leaking into rich production
modules, prevents rich production modules from depending on FX1, and verifies
that production modules do not import later semantic layers.
-/

namespace LeanFX2.Smoke.ImportSurface

#assert_production_import_surface_clean
#assert_rich_production_host_import_surface_clean
#assert_fx1_import_surface_clean
#assert_fx1_core_exact_import_shape
#assert_rich_production_fx1_import_surface_clean
#assert_legacy_lean_kernel_scaffold_isolated
#assert_production_layer_imports_clean
#assert_host_heavy_import_surface_allowlisted
#audit_import_family_summary
#audit_import_surface_summary

end LeanFX2.Smoke.ImportSurface
