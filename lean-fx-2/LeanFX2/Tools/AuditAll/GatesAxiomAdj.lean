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


/-! ## Gates: axiom-adjacent + match-comp (extracted from AuditAll lines 271-302). -/

-- Inhabited / Nonempty / Classical.choice dependent census.  These
-- typeclasses summon Classical.choice internally on certain constructions;
-- counting kernel-tier dependents catches inadvertent uses.  Tight
-- ratchet at zero — nothing in the kernel currently depends on these.
#assert_inhabited_dependent_budget LeanFX2 0

-- HEq result-type theorem census.  Theorems whose claimed result type
-- mentions `HEq` are propext-adjacent — heterogeneous equality cannot
-- generally reduce.  92 today includes the stronger `equivIntroHet`
-- constructor shape with inverse-law proof functions.
#assert_heq_result_type_budget LeanFX2 92

-- Decidable.decide dependent census.  `decide` invokes the kernel
-- reducer on Decidable instances; can hide propext through Decidable
-- on Eq.  390 today includes the stronger `equivIntroHet` constructor
-- shape with inverse-law proof functions and the pointwise proof-function
-- premise on `Term.oeqFunext`, plus the dependent bool eliminator motive.
#assert_decide_dependent_budget LeanFX2 390

-- Subsingleton.elim dependent census.  This is the canonical way to
-- elide Nat.le proof_irrel; sometimes leaks propext on Lean versions
-- that can't reduce through the elision.  Tight ratchet at zero.
#assert_subsingleton_dependent_budget LeanFX2 0

-- Match-compiler equation lemma census.  Auto-generated `_eq_<n>` and
-- `match_<n>` lemmas in kernel-tier namespaces are propext-suspect on
-- indexed inductive families.  Tight ratchet at zero.
#assert_match_compiler_equation_budget LeanFX2 0

-- rfl-only on non-trivial-name theorem census.  Theorems whose name
-- ends in `_inj` / `_unique` / `_iff` / `_def` / `_eq` / `_uniqueProof`
-- with `Eq.refl _` body are heuristic flags for definitionally-trivial
-- restatements masquerading as substantive claims.  Tight ratchet at
-- current count of 1.
#assert_rfl_on_nontrivial_name_budget LeanFX2 1

end LeanFX2.Tools
