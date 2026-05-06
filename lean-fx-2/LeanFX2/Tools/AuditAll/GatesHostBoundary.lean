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

/-! ## GatesHostBoundary — legacy-scaffold + host-boundary + host-heavy allowlist. -/

-- Legacy Lean-kernel scaffold isolation.  The old pre-FX1
-- `LeanFX2.Lean.Kernel.*` module path must stay absent or quarantined while
-- Day 8 targets `LeanFX2.FX1.LeanKernel`.
#assert_legacy_lean_kernel_scaffold_isolated

-- Explicit host-boundary isolation.  Host shims such as `Surface.HostLex`
-- may be imported by smoke/tool modules, but never by the public umbrella or
-- regular production modules.
#assert_host_boundary_isolated

-- Global host-heavy import allowlist.  The only allowed direct host-heavy
-- edge is the audit implementation importing Lean elaborator APIs.
#assert_host_heavy_import_surface_allowlisted

end LeanFX2.Tools
