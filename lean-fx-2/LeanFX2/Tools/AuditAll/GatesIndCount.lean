import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools


/-! ## Gates: inductive-count ratchets+Coe (extracted from AuditAll lines 343-356). -/

-- Inductive ctor-count regression gates.  Pin current ctor count for
-- each load-bearing inductive.  Fails on shrinkage (catches accidental
-- deletion); logs informationally on growth (new constructors).
#assert_inductive_ctor_count_ratchet LeanFX2.Term 78
#assert_inductive_ctor_count_ratchet LeanFX2.Ty 25
#assert_inductive_ctor_count_ratchet LeanFX2.Step 112
#assert_inductive_ctor_count_ratchet LeanFX2.Step.par 133
#assert_inductive_ctor_count_ratchet LeanFX2.RawTerm 74

-- Coe / CoeSort / CoeFun typeclass dependent census.  These silently
-- inject elements between types; a bad Coe makes the type system
-- structurally porous.  Tight ratchet at zero — kernel currently has
-- no Coe family dependents.
#assert_coe_dependent_budget LeanFX2 0

end LeanFX2.Tools
