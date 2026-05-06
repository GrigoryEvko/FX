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


/-! ## Gates: OfNat+Subtype+Eq+Reducible (extracted from AuditAll lines 358-381). -/

-- OfNat / OfScientific dependent census.  OfNat instances let numeric
-- literals inject into types; custom instances on inappropriate types
-- are literal-injection vectors.  530 today reflects pervasive use of
-- Nat literals in proofs plus the stronger `equivIntroHet` constructor
-- shape, pointwise proof-function premise on `Term.oeqFunext`, and the
-- dependent bool eliminator motive.
#assert_ofnat_dependent_budget LeanFX2 530

-- Subtype.mk / Subtype.val dependent census.  Tight ratchet at zero —
-- the kernel doesn't use subtype-encoded reasoning.
#assert_subtype_dependent_budget LeanFX2 0

-- Function.Injective / Bijective / Surjective dependent census.  Tight
-- ratchet at zero — the kernel doesn't use cardinality-based reasoning.
#assert_function_property_dependent_budget LeanFX2 0

-- Eq.symm / Eq.trans / Eq.mp / Eq.recOn / Eq.subst dependent census.
-- 766 today reflects pervasive equality-rewriting in proofs plus the
-- stronger `equivIntroHet` constructor shape and pointwise proof-function
-- premise on `Term.oeqFunext`, plus the dependent bool eliminator motive.
#assert_eq_rewriting_dependent_budget LeanFX2 766

-- Reducible / abbrev kernel decl census.  476 today reflects the
-- Action / Subst / Renaming infrastructure being abbrev-shaped for
-- unification, plus Ty.weaken being @[reducible] per
-- feedback_lean_reducible_weaken.md.  Tight ratchet at current count.
#assert_reducible_decl_budget LeanFX2 476

end LeanFX2.Tools
