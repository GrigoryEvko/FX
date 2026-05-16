import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm.UniversalChain

/-! # AuditConvTransCUniversalChain — CONVTRANS-C Phase A1 audit

Strict gate + reviewer-facing `#print axioms` log for the universal
per-step dispatcher headline `RawStep.par.lift_full_term` and its
supporting predicates (ticket #1734, CONVTRANS-C Phase A1).

## Phase A1 scope

The headline `lift_full_term` assembles the per-ctor
`lift_full_<ctor>` theorems shipped across CONVTRANS-B.{1, 2.*, 3.*}
into a universal Term-induction dispatcher restricted to a
`DispatchAtom` domain (escape hatch (iv) — partial domain).

This Phase A1 commit ships:

* `StepParExists sourceTerm targetRaw` — headline existential
  `Prop`: target type, target Term, typed `Step.par` from source.
* `DispatchAtom sourceTerm` — predicate enumerating the 25
  dispatchable Term ctors:
  * 10 closed-leaf atoms: `unit`, `boolTrue`, `boolFalse`,
    `natZero`, `interval0`, `interval1`, `listNil`, `optionNone`,
    `var`, `universeCode`.
  * 10 type-code ctors: `arrowCode`, `piTyCode`, `sigmaTyCode`,
    `productCode`, `sumCode`, `listCode`, `optionCode`,
    `eitherCode`, `idCode`, `equivCode`.
  * 5 schematic-value ctors: `oeqRefl`, `refl`, `idStrictRefl`,
    `equivReflId`, `equivReflIdAtId`.
* `RawStep.par.lift_full_term dispatch rawStep` — universal driver
  theorem: pattern-matches on `dispatch` and routes through the
  matching `lift_full_<ctor>`.

Phase A1 follow-up commits extend `DispatchAtom` to cover the
remaining clean-dispatchable ctors; wall ctors (`pair`, `appPi`,
`transp`, `hcomp`, `hcompPath`, `funextRefl`, `funextReflAtId`,
`funextIntroHet`, `uaToEquiv`, `equivApply`) remain out-of-domain
for `DispatchAtom` until Phase A2 ships their `lift_full_<ctor>`
variants.

## Three escape hatches — outcome

* Escape hatch (i) **Option form** — explored but rejected:
  `Exists.choose` extraction from the `Prop`-valued `∃` produced by
  the existing `lift_full_<ctor>` theorems is `noncomputable`,
  forbidden by the zero-axiom commitment.
* Escape hatch (ii) **Partial domain** — adopted as
  `DispatchAtom`.  The headline's input includes a `DispatchAtom
  sourceTerm` witness; only `sourceTerm`s in the dispatchable
  family can construct it.  Wall ctors are out-of-domain by
  construction.
* Escape hatch (iii) **Cong-only fallback** — folded into the
  per-ctor lift bodies upstream (e.g. `lift_full_sessionRecv` is
  cong-only); orthogonal to Phase A1 architectural framing.

## Why under Smoke

Same reasoning as the CONVTRANS-B.{1, 2.*, 3.*} audit files:
`Term.PreservesTerm.UniversalChain` is reachable as a production
module only through smoke audits.  Co-location of
`#print axioms` with the strict gate keeps the reviewer-facing log
adjacent.

## Cascade role

* **CONVTRANS-B macro (closed, 13/13)**: 47 of 49 typed β/ι lifts
  shipped.
* **CONVTRANS-C Phase A1 (this commit)**: universal dispatcher
  signature + `DispatchAtom` predicate + 6 closed-leaf atom
  dispatch arms + audit gate.
* **CONVTRANS-C Phase A1 follow-up**: extend `DispatchAtom` to
  ~67 ctors.
* **CONVTRANS-C Phase A2**: re-attempt wall ctors.
* **CONVTRANS-C Phase B**: iterate to `parStar` (#1734 part 2).
* **CONVTRANS-D** (#1735): `Step.subjectReduction` headline.
* **CONVTRANS-Audit** (#1736): strict-gate sweep. -/

namespace LeanFX2.SmokeConvTransCUniversalChain

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if the headline or its
supporting predicates ever reach an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_full_term
#assert_no_axioms LeanFX2.StepParExists
#assert_no_axioms LeanFX2.DispatchAtom

/-! ## Reviewer-facing log — `#print axioms` -/

#print axioms LeanFX2.RawStep.par.lift_full_term
#print axioms LeanFX2.StepParExists
#print axioms LeanFX2.DispatchAtom

end LeanFX2.SmokeConvTransCUniversalChain
