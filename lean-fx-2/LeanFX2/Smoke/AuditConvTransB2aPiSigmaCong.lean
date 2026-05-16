import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB2aPiSigmaCong — CONVTRANS-B.2a Π/Σ cong-family lift audit

Strict-gate plus reviewer-facing audit for the four `RawStep.par.lift_*_cong`
theorems that ship the **Π/Σ cong-family** of CONVTRANS-A subject-reduction
term construction (CONVTRANS-B.2a, ticket #1722).

Each lift produces a typed `Step.par sourceTerm targetTerm` witness from
a raw cong-arm step on a Π or Σ redex parent.  Bodies live in
`Term/PreservesTerm/EliminatorShallowBeta.lean`.

## Coverage

* `lift_app_cong` — non-dep app `Term.app : Ty.arrow domainType codomainType`
* `lift_appPi_cong` — dep app `Term.appPi : Ty.piTy domainType codomainType`
  with codomain depending on argument-raw
* `lift_fst_cong` — Σ first projection at `firstType`
* `lift_snd_cong` — Σ second projection at
  `secondType.subst0 firstType (RawTerm.fst pairRaw)`

## Why "cong" rather than "full"

The full β/β-deep arms of `app`/`appPi`/`fst`/`snd` raw inversions
require destructors that extract canonical lam/lamPi/pair witnesses
from the function/pair IH's typed result.  Those full variants live
under `Term/PreservesTerm/BetaCastWallDemolition.lean` and
`Term/PreservesTerm/HeterogeneousElim.lean` (`lift_full_app`,
`lift_full_fst`, `lift_full_snd`).

`lift_full_appPi` is currently blocked by a structural wall: when the
function IH's typed canonical form is `Term.funextRefl ...` (whose raw
shape is `RawTerm.lam (RawTerm.refl applyRaw)`), the result's type is
`Ty.piTy domainType (Ty.id ...)` — propositionally a `Ty.piTy ...` but
NOT `Term.lamPi`-shaped.  The β-deep typed Step rule `betaAppPiDeep`
demands `Step.par functionTermSource (Term.lamPi bodyTarget)`
specifically, so the funextRefl canonical form falls outside its
coverage.  Closing this gap requires either a new typed Step rule for
`appPi` applied to `funextRefl` or a richer `lamPiDestruct` that
constructs a body witness via `Term.refl` — both deferred to a
subsequent ticket.

## Cascade role

Building block for CONVTRANS-B.2b (closed-type cong: bool/nat/list/
option/either) and the CONVTRANS-C/D headlines that chain raw-typed
lifts through `RawStep.parStar` and ultimately `Conv.trans`
(Phase 7 close-out, #1735).

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB1VacuousLifts.lean`:
`Term.PreservesTerm` is reachable as a production module only through
its smoke audits.  Co-location of `#print axioms` with the strict
gates keeps the reviewer-facing log adjacent.

The `#assert_no_axioms` strict gates fire under the `LeanFX2Audit`
target identically to gates in `Tools/AuditAll/`. -/

namespace LeanFX2.SmokeConvTransB2aPiSigmaCong

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the four Π/Σ cong-family
lifts ever reaches an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_app_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_appPi_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_fst_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_snd_cong

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside the
strict gates above. -/

#print axioms LeanFX2.RawStep.par.lift_app_cong
#print axioms LeanFX2.RawStep.par.lift_appPi_cong
#print axioms LeanFX2.RawStep.par.lift_fst_cong
#print axioms LeanFX2.RawStep.par.lift_snd_cong

end LeanFX2.SmokeConvTransB2aPiSigmaCong
