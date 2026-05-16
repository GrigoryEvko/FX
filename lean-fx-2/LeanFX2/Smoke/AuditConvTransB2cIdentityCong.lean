import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB2cIdentityCong — CONVTRANS-B.2c identity-family cong-only lift audit

Strict gate plus reviewer-facing audit for the three
`RawStep.par.lift_<X>_cong` theorems that ship the **identity-family
cong-only** of CONVTRANS-A subject-reduction term construction
(CONVTRANS-B.2c, ticket #1724).

Each lift takes raw parallel-reduction steps on the base case and
witness subterms together with per-subterm typed-lift callbacks, and
produces a typed `Step.par sourceTerm targetTerm` witness via the
corresponding `Step.par.<X>` cong constructor.  Bodies live in
`Term/PreservesTerm/EliminatorIdentityFamily.lean`.

## Coverage

* `lift_idJ_cong` — HoTT identity J eliminator (`Term.idJ`), witness
  at `Ty.id carrier leftEndpoint rightEndpoint`.
* `lift_oeqJ_cong` — observational-equality J (`Term.oeqJ`), witness
  at `Ty.oeq carrier leftEndpoint rightEndpoint`.
* `lift_idStrictRec_cong` — strict-identity recursor
  (`Term.idStrictRec`), mode-strict gated, witness at
  `Ty.idStrict carrier leftEndpoint rightEndpoint`.

## Why "cong" rather than "full"

The ι-canonical arms (iotaIdJReflDeep / iotaIdStrictRecReflDeep) live
in matching full lifts to be shipped later in the CONVTRANS-B.2
cascade.  oeqJ has no ι-rule in the kernel — its cong-only lift is
the total raw inversion projection.  The cong-only variants assume
the caller has already projected the cong arm of the raw inversion
and just needs to assemble the typed cong rule.

## Cascade role

Mirrors `AuditConvTransB2bClosedTypeCong.lean` for the closed-type
family (ticket #1723) and `AuditConvTransB2aPiSigmaCong.lean` for the
Π/Σ family (ticket #1722).  Together B.2a + B.2b + B.2c cover the
cong-only typed-step construction for every closed-type, arrow/Π/Σ-typed,
and identity-typed eliminator; cubical and modal families
(CONVTRANS-B.2d+) follow the same pattern.

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB2bClosedTypeCong.lean`:
`Term.PreservesTerm` is reachable as a production module only through
its smoke audits.  Co-location of `#print axioms` with the strict
gates keeps the reviewer-facing log adjacent.

The `#assert_no_axioms` strict gates fire under the `LeanFX2Audit`
target identically to gates in `Tools/AuditAll/`. -/

namespace LeanFX2.SmokeConvTransB2cIdentityCong

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the three identity-family
cong-only lifts ever reaches an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_idJ_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_oeqJ_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_idStrictRec_cong

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside the
strict gates above. -/

#print axioms LeanFX2.RawStep.par.lift_idJ_cong
#print axioms LeanFX2.RawStep.par.lift_oeqJ_cong
#print axioms LeanFX2.RawStep.par.lift_idStrictRec_cong

end LeanFX2.SmokeConvTransB2cIdentityCong
