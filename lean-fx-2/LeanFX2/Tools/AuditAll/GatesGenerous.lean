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


/-! ## Gates: 6 generous gates (extracted from AuditAll lines 436-469). -/

-- Lean meta-Expr / MVarId / Syntax / Name / Level dependent census.
-- Production-tier kernel decls should not depend on Lean's
-- metaprogramming data structures.  Initial generous; tightened
-- post-discovery.
#assert_lean_meta_expr_dependent_budget LeanFX2 0

-- Monadic-stack (StateRefT / ReaderT / CoreM / MetaM / etc.) dependent
-- census.  Production decls should be in the kernel, not in tactic /
-- elaboration monads.  Initial generous; tightened post-discovery.
#assert_monadic_stack_dependent_budget LeanFX2 0

-- Heavyweight-tactic dependent census.  omega / aesop / linarith /
-- tauto / simp_all can prove false from inconsistent hypotheses or
-- hide structural reasoning.  Initial generous; tightened
-- post-discovery.
#assert_heavyweight_tactic_dependent_budget LeanFX2 0

-- Smoke-reference coverage lives in `LeanFX2.Smoke.AuditAll`, after the
-- smoke modules are actually loaded.  Running it from Tools/AuditAll only
-- measures the production import cone and reports zero smoke references.

-- absurd / False.elim / False.rec dependent census.  These discharge
-- contradictions; heavy use signals proofs threading through
-- contradictory hypotheses, sometimes vacuously.  529 today includes
-- the stronger `equivIntroHet` constructor shape and pointwise
-- proof-function premise on `Term.oeqFunext`, plus the dependent bool
-- eliminator motive.
#assert_absurd_false_dependent_budget LeanFX2 529

-- Setoid / Quotient (vs primitive Quot) dependent census.  Beyond Quot
-- family, this widens to the equivalence-relation typeclass and the
-- Quotient API on top of Setoid.  Initial generous; tightened
-- post-discovery.
#assert_setoid_quotient_dependent_budget LeanFX2 0

end LeanFX2.Tools
