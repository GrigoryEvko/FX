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


/-! ## Gates: inductive-count ratchets+Coe (extracted from AuditAll lines 343-356). -/

-- Inductive ctor-count regression gates.  Pin current ctor count for
-- each load-bearing inductive.  Fails on shrinkage (catches accidental
-- deletion); logs informationally on growth (codex adding new ctors).
#assert_inductive_ctor_count_ratchet LeanFX2.Term 75
#assert_inductive_ctor_count_ratchet LeanFX2.Ty 25
#assert_inductive_ctor_count_ratchet LeanFX2.Step 105
#assert_inductive_ctor_count_ratchet LeanFX2.Step.par 109
#assert_inductive_ctor_count_ratchet LeanFX2.RawTerm 67

-- Coe / CoeSort / CoeFun typeclass dependent census.  These silently
-- inject elements between types; a bad Coe makes the type system
-- structurally porous.  Tight ratchet at zero — kernel currently has
-- no Coe family dependents.
#assert_coe_dependent_budget LeanFX2 0

end LeanFX2.Tools
