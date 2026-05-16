import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB2bClosedTypeCong — CONVTRANS-B.2b closed-type cong-family lift audit

Strict gate plus reviewer-facing audit for the six
`RawStep.par.lift_<elim>_cong` theorems that ship the **closed-type
cong-family** of CONVTRANS-A subject-reduction term construction
(CONVTRANS-B.2b, ticket #1723).

Each lift takes raw parallel-reduction steps on the scrutinee plus
branches together with per-subterm typed-lift callbacks, and produces
a typed `Step.par sourceTerm targetTerm` witness via the corresponding
`Step.par.<elim>` cong constructor.  Bodies live in
`Term/PreservesTerm/EliminatorConstantMotive.lean`.

## Coverage

* `lift_boolElim_cong` — boolElim with motive at `scope + 1`; output
  type rides on scrutinee target raw via `motiveType.subst0 Ty.bool _`.
* `lift_natElim_cong` — natElim with constant motive at `Ty level scope`.
* `lift_natRec_cong` — natRec with constant motive (recursive succ
  arrow `Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)`).
* `lift_listElim_cong` — listElim with constant motive.
* `lift_optionMatch_cong` — optionMatch with constant motive.
* `lift_eitherMatch_cong` — eitherMatch with constant motive.

## Why "cong" rather than "full"

The full ι-canonical arms (iotaNatElimZeroDeep / iotaListElimNilDeep /
etc.) ship in the matching `lift_<elim>` full variants above the new
cong-only definitions in `EliminatorConstantMotive.lean`.  Those full
variants pay the three-arm `rcases <elim>_inv` dispatch plus the
canonical-form destructors (`Term.natSuccDestruct`, `Term.optionSomeDestruct`,
…) to handle scrutinee parallel-reduction into a constructor head.
The cong-only variant assumes the caller has already projected the
cong arm of the raw inversion and just needs to assemble the typed
cong rule.

## Cascade role

Mirrors `AuditConvTransB2aPiSigmaCong.lean` for the Π/Σ family
(ticket #1722).  Together B.2a + B.2b cover the cong-only typed-step
construction for every closed-type and arrow/Π/Σ-typed eliminator;
the cumul / cubical / HoTT eliminators (CONVTRANS-B.2c+) follow the
same pattern with mode-strict or mode-univalent gating.

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB2aPiSigmaCong.lean` and
`AuditConvTransB1VacuousLifts.lean`: `Term.PreservesTerm` is reachable
as a production module only through its smoke audits.  Co-location of
`#print axioms` with the strict gates keeps the reviewer-facing log
adjacent.

The `#assert_no_axioms` strict gates fire under the `LeanFX2Audit`
target identically to gates in `Tools/AuditAll/`. -/

namespace LeanFX2.SmokeConvTransB2bClosedTypeCong

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the six closed-type
cong-family lifts ever reaches an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_boolElim_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_natElim_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_natRec_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_listElim_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_optionMatch_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_eitherMatch_cong

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside the
strict gates above. -/

#print axioms LeanFX2.RawStep.par.lift_boolElim_cong
#print axioms LeanFX2.RawStep.par.lift_natElim_cong
#print axioms LeanFX2.RawStep.par.lift_natRec_cong
#print axioms LeanFX2.RawStep.par.lift_listElim_cong
#print axioms LeanFX2.RawStep.par.lift_optionMatch_cong
#print axioms LeanFX2.RawStep.par.lift_eitherMatch_cong

end LeanFX2.SmokeConvTransB2bClosedTypeCong
