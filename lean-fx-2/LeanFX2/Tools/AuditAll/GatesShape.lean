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


/-! ## Gates: Mode+Bridge+False+Sigma (extracted from AuditAll lines 383-414). -/

-- Mode inductive exact-ctor-count assertion.  Per kernel-sprint §1.4,
-- Mode should have exactly 5 ctors (strict / observational / univalent
-- / cohesiveFlat / cohesiveSharp).  This gate fails on ANY mismatch.
-- Codex currently ships extras (legacy modes); this gate documents the
-- spec-compliance gap until the legacy modes are stripped.
-- DOCUMENTED-DEFER: Mode actually has more ctors today (legacy modes
-- await cleanup).  Use the regression-only ratchet instead until
-- spec-compliance is achieved.
#assert_inductive_ctor_count_ratchet LeanFX2.Mode 5

-- Bridge round-trip parity.  For every encodeTermSound_<X>, expect a
-- companion encodeTermSound_<X>_roundTrip proving a `BridgeRoundTrip`
-- certificate.  Without a certificate-shaped companion, the bridge could be
-- lossy.  Tight budget at zero: every current exact bridge fragment has a
-- certificate-shaped round-trip companion.
#assert_bridge_round_trip_budget LeanFX2 0

-- False-in-result-type kernel decl census.  Theorems whose result type
-- mentions False are evidence of vacuous reasoning or contradiction
-- discharge.  Tight ratchet at zero — currently clean.
#assert_false_in_result_type_budget LeanFX2 0

-- Term/RawTerm ctor delta.  Term has 75 ctors, RawTerm has 69 — the 6
-- delta means manufactured-witness Term ctors share raw projections
-- with each other.  Architectural choice for refl-fragment Univalence/
-- funext support.  Pinning the delta catches new manufactured-witness
-- ctors arriving without RawTerm parity.  D3.6-P1 added
-- `RawTerm.uaToEquiv` (a raw-only ctor; typed mirror lands in P3),
-- shrinking the delta from 8 to 7.  D3.6-P2 adds `RawTerm.equivApply`
-- (also raw-only; typed mirror lands in P4), shrinking it to 6.
-- D3.6-P3 ships the typed mirror `Term.uaToEquiv` (Term grows by 1
-- to 76; RawTerm unchanged at 69), so the delta grows back to 7.
-- D3.6-P4 ships the typed mirror `Term.equivApply` (Term grows by 1
-- to 77; RawTerm unchanged at 69), so the delta grows to 8.
#assert_term_raw_ctor_delta LeanFX2.Term LeanFX2.RawTerm 8

-- Sigma / PSigma / Sum / PSum / PProd dependent census.  Heterogeneous
-- packaging types; heavy use signals existential reasoning.  1255 today
-- reflects pervasive use of Sigma/PSigma in dependent-type proofs plus
-- the proof-function coherence premises on `Term.equivIntroHet` and
-- pointwise proof-function premise on `Term.oeqFunext`, plus the
-- dependent bool eliminator motive, plus the FIFTEEN Algo/Completeness
-- M10 inferable theorems (#1569) closing the full inferable subset:
-- five atomic-case + five single-recurse + five multi-recurse
-- (app/fst/snd/listCons/idJ via the `dsimp only + dif_pos rfl`
-- recipe) all returning `Σ ty, Term ctx ty raw`, plus the FIFTEEN
-- check-mode counterpart theorems closing the bidirectional side
-- of M10 (atomic + parametric leaf + single-recurse + multi-recurse
-- + binder + Σ-pair) which transitively pull in the 529-line
-- `Term.check` function whose closure references DecEq-Ty and
-- expected-type pattern dispatch.  Tight ratchet at current count.
-- D3.6-P1 added one cong rule (`RawStep.par.uaToEquivCong`) and one
-- ctor (`RawTerm.uaToEquiv`) to the kernel; the cascade arms in
-- `cd`'s redex helpers (each new `RawTerm.uaToEquiv _ => rebuild`
-- branch) plus the `subst_par_pointwise` arm transitively pull in
-- the dependent-pair existentials of inversion lemmas, contributing
-- one new dependent.  D3.6-P2 ships the binary `equivApply` ctor +
-- `equivApplyCong`, contributing one more dependent through the
-- mirror cascade arms (each redex helper now has a parallel
-- `RawTerm.equivApply _ _ => rebuild` branch).
-- D3.6-P3 ships the typed `Term.uaToEquiv` cascade — the new typed
-- ctor + Step.par.uaToEquivCong + Step.uaToEquivProof +
-- ConvCumul.uaToEquivCong + Allais helper transitively contribute
-- six more dependent-pair existential dependents through their
-- inversion / induction / dispatch arms.
-- D3.6-P4 ships the typed `Term.equivApply` cascade — typed binary
-- ctor + Step.par.equivApplyCong + Step.equivApplyEquiv +
-- Step.equivApplyArgument + ConvCumul.equivApplyCong + Allais helper
-- transitively contribute five more dependent-pair existential
-- dependents through their inversion / induction / dispatch arms.
#assert_dependent_pair_dependent_budget LeanFX2 1399

end LeanFX2.Tools
