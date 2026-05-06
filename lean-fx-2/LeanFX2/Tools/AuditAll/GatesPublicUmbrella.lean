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

/-! ## GatesPublicUmbrella — public-umbrella reachability + rich production host import. -/

-- Public umbrella isolation.  Broad entrypoints (`LeanFX2`, `LeanFX2.Kernel`,
-- `LeanFX2.Rich`, `LeanFX2.FX1Bridge`, `LeanFX2.FX1`, `LeanFX2.FX1.Core`) may
-- appear only in the deliberate public-entrypoint chain or in smoke/tooling
-- audits.
#assert_public_umbrella_imports_isolated

-- Rich production host-import gate.  Regular production modules must not
-- import host-heavy modules such as `Lean`, `Std`, `Lake`, `Mathlib`,
-- `Classical`, or host `Quot` directly.  FX1 and tooling are checked by
-- narrower gates below.
#assert_rich_production_host_import_surface_clean

end LeanFX2.Tools
