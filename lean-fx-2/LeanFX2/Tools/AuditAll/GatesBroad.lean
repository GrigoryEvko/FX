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


/-! ## Gates: broad+cast+forbidden+raw (extracted from AuditAll lines 219-269). -/

-- Broad manufactured-Step dependent census.  Wider than the headline
-- refl-fragment gate above: counts ANY decl whose closure mentions a
-- manufactured Univalence/funext rule, except for an allowlist of
-- decls expected to thread those rules structurally (Confluence /
-- RawCd / RawPar / Cd / CdLemma / Diamond / ChurchRosser scaffolding,
-- the headline-named claims already counted, and HoTT/Cubical
-- headline-adjacent files).  Pins current count to catch wrappers
-- that rename-and-restate refl-fragment claims.  Today's 121 count
-- includes Step.par cong rules that name the manufactured rule in
-- their cd-lemma chain; reducing it requires either tightening the
-- allowlist further or replacing manufactured-witness shipping with
-- a general-rule shipping (the latter is the real fix, see
-- WEAK-FX2-03 in the audit).
#assert_broad_manufactured_step_dependent_budget LeanFX2 121

-- Cast-operator dependent census.  Counts kernel-tier decls whose
-- closure references Eq.mpr / Eq.ndrec / Eq.rec / HEq.rec /
-- HEq.ndrec / HEq.subst / cast / Eq.subst / Eq.symm / HEq.symm.
-- These are the heterogeneous-equality cast operators that often
-- hide propext or Quot.sound; a budgeted count makes new casts
-- visible.  Kernel tier covers Term/Foundation/Reduction/Confluence/
-- HoTT/Cubical/Modal/Graded.  860 today includes the stronger
-- `equivIntroHet` constructor shape, pointwise proof-function premise
-- on `Term.oeqFunext`, and row-permission evidence transport on
-- `Term.effectPerform`, plus the dependent bool eliminator motive.
#assert_cast_operator_dependent_budget LeanFX2 860

-- Forbidden decl shape budget.  CLAUDE.md bans `partial def`,
-- `opaque` (without rfl-reducible body), and `unsafe def` for kernel
-- theorems.  This gate scans the kernel tier for those constant-info
-- shapes; budget zero means none should appear (and currently 0 ✓).
#assert_forbidden_decl_shape_budget LeanFX2 0

-- All-raw-payload Term ctor count.  A Term ctor whose every explicit
-- binder type is RawTerm/Nat/UniverseLevel is a typing wrapper around
-- raw syntax.  Today no Term ctor matches because every `*Code` ctor
-- includes a Prop-typed `levelLe` premise, so the count is 0.  Tight
-- ratchet: any future ctor whose every explicit binder is raw will
-- fail the build at this 0 budget.
#assert_all_raw_payload_budget LeanFX2.Term 0

-- Value-shaped type-code constructors.  The all-raw gate misses `*Code`
-- ctors because they carry proof binders; this gate counts `Term.*Code`
-- ctors that still lack recursive typed `Term` children.
#assert_value_type_code_budget LeanFX2.Term 11
#assert_value_type_code_snapshot LeanFX2.Term

-- Single-step Conv claim count.  A theorem whose result type is
-- `Conv ...` and whose body collapses to a single `Conv.fromStep` /
-- `Conv.fromStepStar` is a single-step Conv claim — it asserts
-- convertibility but only via one reduction.  Pinning catches
-- "Theorem X = Conv.fromStep RuleY" claims that pretend more than
-- they prove.  Tight ratchet at current count.
#assert_single_step_conv_claim_budget LeanFX2 32

-- Reduction.Compat per-cong coverage.  For every Step.par.<X>Cong,
-- expect <X>Cong.rename_compatible and <X>Cong.subst_compatible.
-- Without these, parallel-reduction substitution stability fails and
-- the diamond cascade breaks.  Tight ratchet at current count.
#assert_reduction_compat_coverage_budget LeanFX2.Step.par 28

end LeanFX2.Tools
