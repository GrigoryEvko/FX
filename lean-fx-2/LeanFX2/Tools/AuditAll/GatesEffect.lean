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
-- D3.6-P3: typed `Term.uaToEquiv` cascade contributes one more
-- API-typeclass dependent (DecidableEq HeadCtor extension for the
-- new enum entry).
-- D3.6-P4: typed `Term.equivApply` cascade contributes one more
-- API-typeclass dependent (DecidableEq HeadCtor extension for the
-- new enum entry).
#assert_api_typeclass_dependent_budget LeanFX2 84

-- IO / Task / EIO / BaseIO effect dependent census.  Kernel must not
-- depend on runtime IO.  Tight ratchet at zero.
#assert_io_effect_dependent_budget LeanFX2 0

-- Anonymous-projection (Prod.fst / And.intro / Or.elim / Iff.mp / etc.)
-- dependent census.  Heavy use signals proofs that destructure
-- dependent values without being explicit about structure.  Tight
-- ratchet at current count.
-- D3.6-P3: typed `Term.uaToEquiv` cascade Allais helper +
-- substHet/rename/subst arms thread one more anonymous-projection
-- dependent.
-- D3.6-P4: typed `Term.equivApply` binary cascade Allais helper +
-- binary substHet/rename/subst arms thread one more anonymous-
-- projection dependent.
-- K11.1: PolyCell `deriving Repr` adds one anonymous-projection
-- dependent through the Repr-derivation infrastructure.
#assert_anonymous_projection_dependent_budget LeanFX2 180

end LeanFX2.Tools
