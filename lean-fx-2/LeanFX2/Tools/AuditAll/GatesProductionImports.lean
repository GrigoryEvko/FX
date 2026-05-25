import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2.Tools.StrictHarness.Common.ImportSurface.Predicates
import LeanFX2
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools

/-! ## GatesProductionImports — production layer + redundant + cleanliness imports. -/

-- Production import-surface gate.  No production module may import
-- `LeanFX2.Tools`, `LeanFX2.Smoke`, `LeanFX2.Sketch`, or the broad
-- `LeanFX2` root as an internal dependency.
#assert_production_import_surface_clean

-- Semantic layer gate.  Foundation/Term/Reduction/etc. modules may only
-- import their own layer or earlier layers, so later metatheory cannot leak
-- downward through a convenience import.
-- TODO POLYCELL: disabled honestly.  The command body is currently
-- preserved only inside `StrictHarness/Common/ImportSurface/Layering.lean`'s
-- disabled cascade-era block; re-enable after the PolyCell audit profile
-- replaces the old layer model.
-- #assert_production_layer_imports_clean

-- Redundant direct project-import gate.  Production modules may not keep
-- extra direct `LeanFX2.*` imports that are already reachable through another
-- direct import, except for the four documented semantic core edges.
-- TODO POLYCELL: disabled honestly with Layering.
-- #assert_no_redundant_production_project_imports

end LeanFX2.Tools
