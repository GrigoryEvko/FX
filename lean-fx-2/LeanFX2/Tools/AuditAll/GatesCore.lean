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


/-! ## Gates: universe+Quot+Acc+toRaw (extracted from AuditAll lines 304-341). -/

-- Universe-polymorphism leak.  Kernel-tier decls should pin universe
-- levels; `.sort (.param _)` / `.sort (.max ...)` / `.sort (.imax ...)`
-- in result types are universe-polymorphic and can interact with
-- cumulativity in hard-to-audit ways.  527 today is high but reflects
-- the Action / ActsOnRawTerm / ActsOnTyVar typeclass framework being
-- universe-polymorphic by design — not a regression, an architectural
-- choice.  Tight ratchet at current count.
#assert_universe_polymorphism_budget LeanFX2 527

-- Quot / Quotient family dependents.  Quot is propositional truncation;
-- Quot.lift / Quot.ind / Quot.rec are Classical-adjacent (Quot.sound IS
-- an axiom, already separately gated).  Tight ratchet at zero — the
-- kernel currently has no Quot family dependents.
#assert_quot_dependent_budget LeanFX2 0

-- Acc / WellFounded family dependents.  Well-founded recursion can
-- hide non-structural termination; structural recursion is the
-- preferred discipline.  Tight ratchet at zero — the kernel currently
-- relies entirely on structural recursion.
#assert_acc_dependent_budget LeanFX2 0

-- Lean elaboration / metaprogramming dependent census.  Production-tier
-- kernel decls should not depend on Lean.Elab / Lean.Meta / Lean.Parser
-- machinery (those layers belong to tactic mode and parser
-- extensions).  Tight ratchet at zero.
#assert_lean_meta_dependent_budget LeanFX2 0

-- toRaw projection coverage.  Every Term ctor `LeanFX2.Term.<X>` should
-- have `LeanFX2.Term.toRaw_<X>` proving the raw projection equals the
-- index.  This is the core discipline that makes raw-aware Term work.
-- Tight ratchet at zero — full coverage today, must remain.
#assert_toraw_coverage_budget LeanFX2.Term 0

-- IsClosedTy parity.  For every scope-independent Ty constructor (unit,
-- bool, nat, arrow, listType, optionType, eitherType, universe, empty,
-- interval, equiv, record, codata, modal — 14 ctors), expect a
-- same-suffix IsClosedTy ctor.  Tight ratchet at zero — full parity.
#assert_is_closed_ty_parity_budget LeanFX2.Ty 0

end LeanFX2.Tools
