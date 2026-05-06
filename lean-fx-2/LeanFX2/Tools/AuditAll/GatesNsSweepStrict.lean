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

/-! ## GatesNsSweepStrict — aggregate strict-discipline namespace sweep. -/

-- Aggregate strict gate.  Walks the same loaded production decls and
-- flags every discipline violation in one error, including
-- `noncomputable`, `@[extern]`, `@[implemented_by]`, and direct
-- `Classical.*` references.  Subsumes `#audit_namespace` (which only
-- looks at axioms) but kept side-by-side as defense in depth.  Runs
-- as its own sibling file so Lake parallelizes it with the axiom
-- sweep above.
#audit_namespace_strict LeanFX2

end LeanFX2.Tools
