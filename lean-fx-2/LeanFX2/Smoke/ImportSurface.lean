import LeanFX2
import LeanFX2.Tools.StrictHarness

/-! # Smoke/ImportSurface — production import-boundary gate.

This smoke imports the public umbrella and then checks the direct
imports of every production `LeanFX2.*` module visible in that broad
environment.  Production modules may not import `Smoke`, `Tools`,
`Sketch`, or the broad `LeanFX2` root.
-/

namespace LeanFX2.Smoke.ImportSurface

#assert_production_import_surface_clean

end LeanFX2.Smoke.ImportSurface
