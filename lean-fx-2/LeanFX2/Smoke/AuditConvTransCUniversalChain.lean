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

This commit ships (current coverage 58/78 Term ctors):

* `StepParExists sourceTerm targetRaw` — headline existential
  `Prop`: target type, target Term, typed `Step.par` from source.
* `DispatchAtom sourceTerm` — predicate enumerating the
  dispatchable Term ctors.  Initial Phase A1 carried 25 ctors
  (10 closed-leaf atoms + 10 type-code ctors + 5 schematic-value
  ctors).  Phase A1 follow-up commits extended to 58 ctors,
  adding closed-type cong arms (arrow/list/option/either/nat),
  Π-cong arms (lam/lamPi/app), record/codata/refine/glue
  ctors, modal arms (modIntro/modElim/subsume × 8 modalities),
  identity-type ctors (id/idStrict/oeq leaves), boolElim
  (with per-branch closure witnesses), equivIntroHet, and the
  schematic funext ctors (funextRefl, funextReflAtId).
* `RawStep.par.lift_full_term dispatch rawStep` — universal driver
  theorem: pattern-matches on `dispatch` and routes through the
  matching `lift_full_<ctor>`.

Remaining 20 ctors (fst/snd/idJ/oeqJ/idStrictRec/refineElim/
glueElim/pathApp/effectPerform/sessionRecv/sessionSend/oeqFunext
+ 8 leaf-needing ctors pair/funextIntroHet/uaToEquiv/equivApply/
appPi/transp/hcomp/hcompPath) are blocked on structural
infrastructure:

* fst/snd need a sigma-preservation lemma; the analogue of
  `Step.par.preserves_isClosedTy` is FALSE for non-closed
  `secondType : Ty level (scope + 1)` because boolElim-style
  cong rules reduce `motiveType.subst0 _ raw1 = Ty.sigmaTy fst snd`
  to `motiveType.subst0 _ raw2` where `snd` may depend on var 0.
* idJ/oeqJ/idStrictRec/refineElim/glueElim/pathApp need
  per-type-former preservation lemmas (id/refine/glue/path).
* effectPerform/sessionRecv/sessionSend need closure witnesses
  on effect-row / session-protocol payloads.
* The 8 leaf-needing ctors require new `lift_full_<ctor>`
  shipped first.

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
#assert_no_axioms LeanFX2.RawStep.par.lift_full_pair
#assert_no_axioms LeanFX2.RawStep.par.lift_full_hcomp

/-! ## Reviewer-facing log — `#print axioms` -/

#print axioms LeanFX2.RawStep.par.lift_full_term
#print axioms LeanFX2.StepParExists
#print axioms LeanFX2.DispatchAtom
#print axioms LeanFX2.RawStep.par.lift_full_pair
#print axioms LeanFX2.RawStep.par.lift_full_hcomp

end LeanFX2.SmokeConvTransCUniversalChain
