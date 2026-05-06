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

/-! ## GatesNsSweepAxiom — broad axiom-only namespace sweep. -/

-- Loaded production namespace sweep.  `#audit_namespace` excludes
-- `LeanFX2.Tools` and `LeanFX2.Smoke`, so this is the broad fail-fast
-- gate for every production declaration imported above, not a
-- replacement for targeted smoke examples.  Each kernel decl's
-- transitive closure is checked for any leaked Lean axiom or
-- user-declared axiom.
#audit_namespace LeanFX2

end LeanFX2.Tools
