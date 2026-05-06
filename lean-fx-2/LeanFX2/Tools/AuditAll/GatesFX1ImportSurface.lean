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

/-! ## GatesFX1ImportSurface — FX1 / FX1.Core / FX1.LeanKernel host-minimal + DAG shape. -/

-- FX1/Core host-minimal gate.  This is intentionally scoped to the
-- future minimal-root namespace, not the rich kernel: FX1 declarations
-- must not depend on host-heavy `Lean`, `Std`, `Classical`, host `Quot`,
-- `propext`, `Classical.choice`, `Quot.sound`, `Quot.lift`, or `sorryAx`.
-- It succeeds with zero declarations, so it can be wired before FX1/Core
-- exists and will begin enforcing as soon as FX1 files are imported.
#assert_fx1_core_host_minimal LeanFX2.FX1

-- FX1 direct-import gate.  FX1/Core may only import FX1/Core;
-- FX1/LeanKernel may only import FX1/Core or FX1/LeanKernel.  Like the
-- host-minimal gate, this passes with zero FX1 modules and begins enforcing
-- as soon as the namespace is loaded.
#assert_fx1_import_surface_clean

-- Exact FX1/Core root-DAG gate.  This is stricter than "FX1 imports only
-- FX1": it prevents a minimal-root leaf from importing the Core umbrella or a
-- later metatheory module without an explicit policy update.
#assert_fx1_core_exact_import_shape

-- Exact FX1/LeanKernel DAG gate.  The Lean-kernel model over FX1 is allowed
-- to exist, but every direct dependency edge must be intentional.
#assert_fx1_lean_kernel_exact_import_shape

-- Rich production / FX1 separation.  FX1 is the future minimal TCB root;
-- rich production modules may not import it directly until a deliberate
-- bridge/certificate boundary exists.
#assert_rich_production_fx1_import_surface_clean

end LeanFX2.Tools
