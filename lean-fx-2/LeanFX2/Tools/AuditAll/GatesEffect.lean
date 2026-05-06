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


/-! ## Gates: Classical+API+IO+AnonProj (extracted from AuditAll lines 416-434). -/

-- Classical.choose / em / byContradiction dependent census.  Refines
-- the Inhabited gate by naming the canonical excluded-middle
-- operations.  Tight ratchet at zero — kernel doesn't use Classical.
#assert_classical_reasoning_dependent_budget LeanFX2 0

-- Hashable / Repr / ToString / BEq / Format dependent census.  These
-- are user-facing API typeclasses; kernel decls should NOT depend on
-- them.  5 today is minor leakage; tight ratchet at current.
#assert_api_typeclass_dependent_budget LeanFX2 5

-- IO / Task / EIO / BaseIO effect dependent census.  Kernel must not
-- depend on runtime IO.  Tight ratchet at zero.
#assert_io_effect_dependent_budget LeanFX2 0

-- Anonymous-projection (Prod.fst / And.intro / Or.elim / Iff.mp / etc.)
-- dependent census.  Heavy use signals proofs that destructure
-- dependent values without being explicit about structure.  Tight
-- ratchet at current count.
#assert_anonymous_projection_dependent_budget LeanFX2 174

end LeanFX2.Tools
