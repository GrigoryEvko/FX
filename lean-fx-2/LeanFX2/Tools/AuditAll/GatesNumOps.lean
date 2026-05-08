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
-- are literal-injection vectors.  843 today reflects pervasive use of
-- Nat literals in proofs plus the stronger `equivIntroHet` constructor
-- shape, pointwise proof-function premise on `Term.oeqFunext`, the
-- dependent bool eliminator motive, and the FIFTEEN Algo/Completeness
-- M10 inferable theorems closing the full inferable subset (atomic +
-- single-recurse + multi-recurse) whose closure transitively pulls in
-- `Term.infer`, plus the FIFTEEN M10 check-mode theorems whose closure
-- transitively pulls in `Term.check` (which itself references OfNat
-- via the Nat-indexed Fin scope position dispatch).
#assert_ofnat_dependent_budget LeanFX2 866

-- Subtype.mk / Subtype.val dependent census.  Tight ratchet at zero —
-- the kernel doesn't use subtype-encoded reasoning.
#assert_subtype_dependent_budget LeanFX2 0

-- Function.Injective / Bijective / Surjective dependent census.  Tight
-- ratchet at zero — the kernel doesn't use cardinality-based reasoning.
#assert_function_property_dependent_budget LeanFX2 0

-- Eq.symm / Eq.trans / Eq.mp / Eq.recOn / Eq.subst dependent census.
-- 1079 today reflects pervasive equality-rewriting in proofs plus the
-- stronger `equivIntroHet` constructor shape and pointwise proof-function
-- premise on `Term.oeqFunext`, plus the dependent bool eliminator motive,
-- plus the FIFTEEN Algo/Completeness M10 inferable theorems closing
-- the full inferable subset (atomic + single-recurse + multi-recurse
-- including the dsimp-only/dif_pos-rfl recipe for app/listCons)
-- pulling in `Term.infer`, plus the FIFTEEN M10 check-mode counterpart
-- theorems whose closure threads `h ▸ t` (which expands through
-- Eq.rec) on every expected-type-equality arm of `Term.check`.
#assert_eq_rewriting_dependent_budget LeanFX2 1102

-- Reducible / abbrev kernel decl census.  476 today reflects the
-- Action / Subst / Renaming infrastructure being abbrev-shaped for
-- unification, plus Ty.weaken being @[reducible] per
-- feedback_lean_reducible_weaken.md.  Tight ratchet at current count.
#assert_reducible_decl_budget LeanFX2 476

end LeanFX2.Tools
