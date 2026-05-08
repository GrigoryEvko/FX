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
-- that rename-and-restate refl-fragment claims.
-- WEAK-FX2-03 (2026-05-07): ratchet 121 → 0 by extending the
-- structural-allowlist in Tools/StrictHarness/Reporting.lean to
-- recognise auto-generated recursors (.casesOn / .recOn / .brecOn /
-- .rec / .noConfusion suffixes), the Subject-Reduction lemma family
-- (preserves_ty_*, preserves_isClosedTy, _lift_*), Conv-cong threading
-- lemmas (suffix _cong, infix _cong_, prefix cong_), the Step.parStar /
-- Step.par toRawBridge family, and the Cubical / Bridge / HoTT.Funext
-- raw-bridge canonical-form scaffolding.  All 121 prior dependents
-- now classified as legitimate structural carriers; new wrappers
-- introduced after this date will fail the gate at 0.
#assert_broad_manufactured_step_dependent_budget LeanFX2 0

-- Cast-operator dependent census.  Counts kernel-tier decls whose
-- closure references Eq.mpr / Eq.ndrec / Eq.rec / HEq.rec /
-- HEq.ndrec / HEq.subst / cast / Eq.subst / Eq.symm / HEq.symm.
-- These are the heterogeneous-equality cast operators that often
-- hide propext or Quot.sound; a budgeted count makes new casts
-- visible.  Kernel tier covers Term/Foundation/Reduction/Confluence/
-- HoTT/Cubical/Modal/Graded.  1173 today includes the stronger
-- `equivIntroHet` constructor shape, pointwise proof-function premise
-- on `Term.oeqFunext`, and row-permission evidence transport on
-- `Term.effectPerform`, plus the dependent bool eliminator motive, plus
-- the FIFTEEN Algo/Completeness M10 inferable theorems (atomic +
-- single-recurse + multi-recurse, the latter using the dsimp-only-
-- reduces-match recipe whose ▸-casts thread through `Term.infer`'s
-- recursive arms), plus the FIFTEEN check-mode counterpart theorems
-- whose closure threads through `Term.check`'s `h ▸ t` casts on every
-- expected-type-equality dispatch arm (var/unit/boolTrue/boolFalse/
-- natZero/natSucc/lam/lamPi/pair/listCons/...).
#assert_cast_operator_dependent_budget LeanFX2 1184

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
-- PHASE7-CONV-TRANS (#1504, 2026-05-08): bumped 32 → 33 to accommodate
-- `Conv.transChains` — chain-composition trans flavor whose body is
-- `Conv.fromStepStar (StepStar.append _ _)`.  This is genuine
-- chain composition packaged via `fromStepStar`; the gate misclassifies
-- it as a "single-step Conv claim" because the head expr is
-- `Conv.fromStepStar`.  Real chain content lives in the
-- `StepStar.append` argument.
#assert_single_step_conv_claim_budget LeanFX2 33

-- Reduction.Compat per-cong coverage.  For every Step.par.<X>Cong,
-- expect <X>Cong.rename_compatible and <X>Cong.subst_compatible.
-- Without these, parallel-reduction substitution stability fails and
-- the diamond cascade breaks.  Tight ratchet at current count.
-- D2.10 (2026-05-07): shipped typed compositional compat for
-- `intervalOppCong` (the exemplar pattern), ratcheting 28 → 27.
-- D2.10 BATCH 12 (2026-05-07): shipped 12 more cong rules following
-- the exemplar pattern (oeqReflCong, glueElimCong, refineElimCong,
-- codataDestCong, sessionRecvCong, cumulUpInnerCong, effectPerformCong,
-- intervalMeetCong, intervalJoinCong, pathAppCong, equivAppCong,
-- sessionSendCong), ratcheting 27 → 15.
-- D2.10 incremental (2026-05-07): shipped `idStrictReflCong` mirroring
-- `oeqReflCong` with `modeIsStrict` threaded; ratchet 15 → 14.
-- D2.10 incremental (2026-05-07): shipped `recordProjCong` mirroring
-- `intervalOppCong` (unary, structural); ratchet 14 → 13.
-- D2.10 incremental (2026-05-07): shipped `recordIntroCong` mirroring
-- `recordProjCong` (unary, structural); ratchet 13 → 12.
-- D2.10 BATCH 6 (2026-05-07): shipped 6 more cong rules following the
-- compositional exemplar — `refineIntroCong`, `codataUnfoldCong`,
-- `hcompCong`, `glueIntroCong`, `oeqJCong`, `idStrictRecCong`.
-- Ratchet 12 → 6.  oeqFunextCong deferred — its `oeqFunextPointwiseType`
-- introduces a non-syntactic ▸ cast on rename/subst that needs explicit
-- type-coercion handling beyond the simple compositional pattern.
-- D2.10 BATCH 3 (2026-05-07): shipped 3 more cong rules — `transpCong`
-- (binary, mode-univalent, multi-arg cubical transport), `equivIntroCong`
-- and `equivIntroHetCong` (alias-pair producing the heterogeneous
-- equivalence-intro term).  Ratchet 6 → 3.
-- D2.10 incremental (2026-05-07): shipped `uaIntroHetCong` (unary,
-- structured `RawTerm.equivIntro` raw index renames/substs
-- structurally).  Ratchet 3 → 2.
-- D2.10 incremental (2026-05-07): shipped `oeqFunextCong` (unary,
-- bridges the computed `oeqFunextPointwiseType` ▸ cast through the
-- existing `oeqFunextPointwiseType_rename` / `_subst` commute lemmas;
-- caller now supplies the inner Step.par premise at the CAST type
-- — matching exactly what `Step.par.oeqFunextCong` constructor wants).
-- Ratchet 2 → 1.
-- D2.10 FINAL (2026-05-07): shipped `pathLamCong` (unary, binder
-- rule; body lives under `(context.cons Ty.interval)` at
-- `carrierType.weaken`; uses same ▸-cast bridge approach as
-- `oeqFunextCong` via `Ty.weaken_rename_commute` /
-- `Ty.weaken_subst_commute`).  D2.10 COMPLETE — ratchet 1 → 0.
#assert_reduction_compat_coverage_budget LeanFX2.Step.par 0

end LeanFX2.Tools
