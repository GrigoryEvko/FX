import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB2dModalCong — CONVTRANS-B.2d modal-family cong-only lift audit

Strict gate plus reviewer-facing audit for the three
`RawStep.par.lift_<X>_cong` theorems that ship the **modal-family
cong-only** of CONVTRANS-A subject-reduction term construction
(CONVTRANS-B.2d, ticket #1725).

Each lift takes a raw parallel-reduction step on the single inner
subterm together with a typed-lift callback, and produces a typed
`Step.par sourceTerm targetTerm` witness via the corresponding
`Step.par.<X>` cong constructor.  Bodies live in
`Term/PreservesTerm/EliminatorModalFamily.lean`.

## Coverage

* `lift_modIntro_cong` — modal introduction (`Term.modIntro`).
* `lift_modElim_cong` — modal elimination cong arm (`Term.modElim`).
* `lift_subsume_cong` — cumul subsumption (`Term.subsume`).

## Why "cong" rather than "full"

`modElim`'s raw inversion admits a β disjunct
(`betaModElimIntro` / `betaModElimIntroDeep`) that fires when the
inner value develops to a `modIntro`; the β-arm lives in a future
full lift.  `modIntro` and `subsume` have no β-arm — their cong-only
lifts ARE the total raw inversion projection.

## Cascade role

Mirrors `AuditConvTransB2cIdentityCong.lean` for the identity-family
(ticket #1724), `AuditConvTransB2bClosedTypeCong.lean` for the
closed-type family (ticket #1723), and `AuditConvTransB2aPiSigmaCong.lean`
for the Π/Σ family (ticket #1722).  Modal is the structurally simplest
cong family — single inner subterm per ctor.  Together B.2a + B.2b +
B.2c + B.2d cover the cong-only typed-step construction for Π/Σ,
closed-type, identity-type, and modal eliminators; cubical and
record/refine/codata/session/effect families (CONVTRANS-B.2e+)
follow the same pattern.

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB2cIdentityCong.lean`:
`Term.PreservesTerm` is reachable as a production module only through
its smoke audits.  Co-location of `#print axioms` with the strict
gates keeps the reviewer-facing log adjacent.

The `#assert_no_axioms` strict gates fire under the `LeanFX2Audit`
target identically to gates in `Tools/AuditAll/`. -/

namespace LeanFX2.SmokeConvTransB2dModalCong

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the three modal-family
cong-only lifts ever reaches an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_modIntro_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_modElim_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_subsume_cong

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside the
strict gates above. -/

#print axioms LeanFX2.RawStep.par.lift_modIntro_cong
#print axioms LeanFX2.RawStep.par.lift_modElim_cong
#print axioms LeanFX2.RawStep.par.lift_subsume_cong

end LeanFX2.SmokeConvTransB2dModalCong
