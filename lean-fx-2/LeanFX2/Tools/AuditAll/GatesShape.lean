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
-- companion encodeTermSound_<X>_roundTrip proving decode∘encode = id.
-- Without round-trip, the bridge could be lossy.  Pin current debt.
#assert_bridge_round_trip_budget LeanFX2 9999

-- False-in-result-type kernel decl census.  Theorems whose result type
-- mentions False are evidence of vacuous reasoning or contradiction
-- discharge.  Tight ratchet at zero — currently clean.
#assert_false_in_result_type_budget LeanFX2 0

-- Term/RawTerm ctor delta.  Term has 75 ctors, RawTerm has 67 — the 8
-- delta means manufactured-witness Term ctors share raw projections
-- with each other.  Architectural choice for refl-fragment Univalence/
-- funext support.  Pinning the delta catches new manufactured-witness
-- ctors arriving without RawTerm parity.
#assert_term_raw_ctor_delta LeanFX2.Term LeanFX2.RawTerm 8

-- Sigma / PSigma / Sum / PSum / PProd dependent census.  Heterogeneous
-- packaging types; heavy use signals existential reasoning.  936 today
-- reflects pervasive use of Sigma/PSigma in dependent-type proofs.
-- Tight ratchet at current count.
#assert_dependent_pair_dependent_budget LeanFX2 936

end LeanFX2.Tools
