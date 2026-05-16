import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB1VacuousLifts — CONVTRANS-B.1 vacuous lift audit

Strict-gate plus reviewer-facing audit for the twelve
`RawStep.par.lift_` theorems that ship the **var + value/atom family**
of CONVTRANS-A subject-reduction term construction (CONVTRANS-B.1,
ticket #1721).

Each lift produces a typed `Step.par sourceTerm targetTerm` witness
from a raw step on a value-shaped source raw form.  Bodies live in
`Term/PreservesTerm/TierZeroAndUnary.lean` (10 truly-vacuous atom
lifts) and `Term/PreservesTerm/SchematicValueCtors.lean` (2 schematic-
value lifts at `RawTerm.equivIntro` shape).

## Why "vacuous"

For the ten atom ctors (`unit`, `boolTrue`, `boolFalse`, `natZero`,
`listNil`, `optionNone`, `interval0`, `interval1`, `var`,
`universeCode`), the only `RawStep.par` rule firing on the source raw
form is `RawStep.par.refl`.  Hence the target raw equals the source
raw, and the typed target term is the source itself with
`Step.par.refl sourceTerm`.

For the two schematic-value ctors (`equivReflId`, `equivReflIdAtId`),
the source raw form is `RawTerm.equivIntro (lam (var 0)) (lam (var
0))`.  Although `equivIntro` admits a cong rule in principle, the
`lam (var 0)` payload's children (var, lam) are themselves atom-shaped
and force the par-step to be refl through chained inversion
(`equivIntro_inv → lam_inv → var_inv`).  The typed target collapses
to the source.

## Cascade role

Building block for CONVTRANS-B.2* (non-vacuous cong / β / ι
families) and the CONVTRANS-C/D headlines that chain raw-typed lifts
through `RawStep.parStar` and ultimately `Conv.trans` (Phase 7
close-out, #1735).

## Why this audit lives under Smoke instead of Tools/AuditAll

`Term.PreservesTerm` is reachable as a production module only through
its smoke audits.  Adding the dependency to `Tools/AuditAll/AuditReduction`
triggers the public-umbrella reachability gate in
`Smoke/ImportEverywhere` because the production `LeanFX2.Rich`
umbrella does not currently re-export `Term.PreservesTerm.*`.  The
canonical pattern for axiom gates over PreservesTerm decls is to
co-locate them with the corresponding smoke file, mirroring
`Smoke/AuditPhase1590CorePreservesTerm.lean`.

The `#assert_no_axioms` strict gates fire here under the `LeanFX2Audit`
target identically to gates in `Tools/AuditAll/`; co-location with
`#print axioms` keeps the reviewer-facing log adjacent. -/

namespace LeanFX2.SmokeConvTransB1VacuousLifts

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the twelve lifts ever
reaches an axiom.  Mirrors the per-decl strict-gate coverage style of
`Tools/AuditAll/AuditReduction.lean`. -/

-- Ten truly-vacuous atom lifts (no sub-children that could step).
#assert_no_axioms LeanFX2.RawStep.par.lift_unit
#assert_no_axioms LeanFX2.RawStep.par.lift_boolTrue
#assert_no_axioms LeanFX2.RawStep.par.lift_boolFalse
#assert_no_axioms LeanFX2.RawStep.par.lift_natZero
#assert_no_axioms LeanFX2.RawStep.par.lift_listNil
#assert_no_axioms LeanFX2.RawStep.par.lift_optionNone
#assert_no_axioms LeanFX2.RawStep.par.lift_interval0
#assert_no_axioms LeanFX2.RawStep.par.lift_interval1
#assert_no_axioms LeanFX2.RawStep.par.lift_var
#assert_no_axioms LeanFX2.RawStep.par.lift_universeCode

-- Two schematic-value lifts at RawTerm.equivIntro shape.
#assert_no_axioms LeanFX2.RawStep.par.lift_full_equivReflId
#assert_no_axioms LeanFX2.RawStep.par.lift_full_equivReflIdAtId

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside the
strict gates above. -/

-- Ten truly-vacuous atom lifts.
#print axioms LeanFX2.RawStep.par.lift_unit
#print axioms LeanFX2.RawStep.par.lift_boolTrue
#print axioms LeanFX2.RawStep.par.lift_boolFalse
#print axioms LeanFX2.RawStep.par.lift_natZero
#print axioms LeanFX2.RawStep.par.lift_listNil
#print axioms LeanFX2.RawStep.par.lift_optionNone
#print axioms LeanFX2.RawStep.par.lift_interval0
#print axioms LeanFX2.RawStep.par.lift_interval1
#print axioms LeanFX2.RawStep.par.lift_var
#print axioms LeanFX2.RawStep.par.lift_universeCode

-- Two schematic-value lifts.  Already mirrored in
-- `Smoke/AuditPhase1590CorePreservesTerm.lean`; repeated here for
-- namespace-local CONVTRANS-B.1 coverage closure.
#print axioms LeanFX2.RawStep.par.lift_full_equivReflId
#print axioms LeanFX2.RawStep.par.lift_full_equivReflIdAtId

end LeanFX2.SmokeConvTransB1VacuousLifts
