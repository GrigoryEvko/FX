import LeanFX2
import LeanFX2.Tools.StrictHarness

/-! # Smoke/ImportSurface — production import-boundary gate.

This smoke imports the public umbrella and then checks the direct imports of
every visible public-production `LeanFX2.*` module.  Production modules may not
import `Smoke`, `Tools`, `Sketch`, or the broad `LeanFX2` root.  The same broad
environment also checks future FX1 source imports and prevents the legacy
`LeanFX2.Lean.Kernel` scaffold from leaking into rich production modules.
-/

namespace LeanFX2.Smoke.ImportSurface

#assert_production_import_surface_clean
#assert_fx1_import_surface_clean
#assert_legacy_lean_kernel_scaffold_isolated

end LeanFX2.Smoke.ImportSurface
