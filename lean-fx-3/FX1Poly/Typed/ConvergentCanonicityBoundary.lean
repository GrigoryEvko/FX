import FX1Poly.Core.RawIotaEtaFullStepSN
import FX1Poly.Typed.RawIotaEtaOperationalSN

/-! # FX1Poly/Typed/ConvergentCanonicityBoundary
    — the convergent ι∪η presentation does NOT yield canonicity: its normal forms include
    non-canonical β-redexes (the word/RPO-leg canonicity endpoint is irreducibly β-dependent)

The combinatorial recursive-path-order / convergent-word-system leg proves strong normalization of the
full ι∪η reduction on its OWN order, Tait-free (`iotaEtaFullStep_wellFounded` /
`iotaEta_noInfiniteReduction`).  A natural hope is that this convergent presentation also delivers
CANONICITY — that a closed term in convergent-normal form is a value (constructor-headed).  This file
proves it CANNOT, and pins exactly why.

## The witness

`appLamUnit := app (lam unit) unit` — a closed β-redex.  Two facts about it:

  * **It is ι∪η-NORMAL** (`appLamUnit_iotaEtaNormal`): no `IotaEtaStep` fires.  The root is an `app`, which
    is neither an ι head-redex (the 16 ι arms are all eliminator/projection heads) nor an η head-redex (the
    5 η arms are lam/pair/pathLam/modIntro/glueIntro heads); the only congruence child `lam unit` is itself
    ι∪η-normal (its body `unit` is not an `app`, so the function-η rule cannot fire on it), and `unit` is a
    nullary leaf.  So the convergent presentation HALTS on `appLamUnit` and reports it as a normal form.

  * **It is NOT canonical** (`appLamUnit_betaStepsToUnit`): it β-reduces — `Step appLamUnit unit` — to the
    genuine value `unit`.  So it is not a β-normal form and not a constructor-headed value.

Therefore the convergent ι∪η presentation's normal forms are NOT canonical values.  Canonicity needs
β-normalization (reaching a value through β), and β is exactly what the convergent presentation EXCLUDES:
raw β is non-strongly-normalizing (the Ω combinator self-loops), so β is Tait-imported, not part of the
ι∪η word system.  The word/RPO leg's canonicity endpoint is therefore irreducibly β-dependent — it cannot
be obtained "independently" from the convergent presentation alone.  This is the honest reason that cell of
the metatheory parity ledger stays open research.

## What this ships

  * `unit_iotaEtaNormal` / `appLamUnit_iotaEtaNormal` — the ι∪η-normality witnesses (scope-polymorphic unit
    leaf + the closed β-redex), via the propext-clean `IotaEtaStep` / `IotaHeadStep` / `Step.eta` inversion.
  * `appLamUnit_betaStepsToUnit` — the β-step exhibiting non-canonicity.
  * **`convergentNormalFormNeedNotBeCanonical` (★)** — the headline: a closed term that is ι∪η-normal yet
    `Step`-reduces (to a value), so the convergent presentation's normal forms are not canonical.
  * `convergentNormalFormCanStillBeStronglyNormalizing` — the consistency note: the same witness is of course
    ι∪η-strongly-normalizing (every raw term is), so the gap is precisely between ι∪η-normality and
    canonicity, not between SN and canonicity.

## Zero-axiom verification

The ι∪η-normality inversions are direct `cases` on `IotaEtaStep` / `IotaHeadStep` / `Step.eta` over a closed
term whose root head generator (`gen_app` / `gen_lam` / `gen_unit`) matches no redex arm — Lean prunes the
non-unifying constructors with no equation lemmas, so no `propext` leaks (verified per-declaration).  The
β-step is the single `Step.beta` constructor with `subst0 unit unit = unit` definitional.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- The nullary `unit` leaf admits no ι∪η step, at any scope (the congruence children bottom out here). -/
theorem unit_iotaEtaNormal {scope : Nat} :
    ∀ reduct, ¬ IotaEtaStep (.mkGen .gen_unit () .childNil : RawTerm scope) reduct := by
  intro reduct step
  cases step with
  | head rootStep => cases rootStep with
    | inl iotaHead => cases iotaHead
    | inr etaStep => cases etaStep
  | cong gen payload childStep => cases childStep

/-- `lam unit` admits no ι∪η step: its body `unit` is not an `app`, so the function-η rule does not fire,
and the only congruence child reduces to the `unit` leaf. -/
theorem lamUnit_iotaEtaNormal :
    ∀ reduct, ¬ IotaEtaStep
      (.mkGen .gen_lam () (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm 0) reduct := by
  intro reduct step
  cases step with
  | head rootStep => cases rootStep with
    | inl iotaHead => cases iotaHead
    | inr etaStep => cases etaStep
  | cong gen payload childStep =>
      cases childStep with
      | here rest childStep => exact unit_iotaEtaNormal _ childStep
      | there headChild restStep => cases restStep

/-- **The closed β-redex `app (lam unit) unit` is ι∪η-NORMAL** — the convergent presentation halts on it.
Root `app` matches no ι/η head-redex; the function child `lam unit` and the argument `unit` are each
ι∪η-normal. -/
theorem appLamUnit_iotaEtaNormal :
    ∀ reduct, ¬ IotaEtaStep
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons (.mkGen .gen_unit () .childNil) .childNil))
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm 0) reduct := by
  intro reduct step
  cases step with
  | head rootStep => cases rootStep with
    | inl iotaHead => cases iotaHead
    | inr etaStep => cases etaStep
  | cong gen payload childStep =>
      cases childStep with
      | here rest childStep => exact lamUnit_iotaEtaNormal _ childStep
      | there headChild restStep =>
          cases restStep with
          | here rest2 childStep2 => exact unit_iotaEtaNormal _ childStep2
          | there headChild2 restStep2 => cases restStep2

/-- **The same term β-reduces to the value `unit`** — so it is NOT a canonical value / not β-normal. -/
theorem appLamUnit_betaStepsToUnit :
    Step
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons (.mkGen .gen_unit () .childNil) .childNil))
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm 0)
      (.mkGen .gen_unit () .childNil) :=
  Step.beta

/-- **★ The convergent ι∪η presentation does not imply canonicity.**  There is a closed term that the
convergent presentation classifies as NORMAL (no `IotaEtaStep` fires) yet which still `Step`-reduces — to
the value `unit` — so it is not a canonical value.  Canonicity requires β-normalization, and β is excluded
from the convergent ι∪η word system (raw β is non-SN, Tait-imported).  Hence the word/RPO leg's canonicity
endpoint cannot be obtained independently from the convergent presentation. -/
theorem convergentNormalFormNeedNotBeCanonical :
    ∃ (closedTerm value : RawTerm 0),
      (∀ reduct, ¬ IotaEtaStep closedTerm reduct) ∧ Step closedTerm value :=
  ⟨_, _, appLamUnit_iotaEtaNormal, appLamUnit_betaStepsToUnit⟩

/-- Consistency note: the witness is of course ι∪η-strongly-normalizing (every raw term is), so the gap is
precisely between ι∪η-NORMALITY and canonicity — not between strong normalization and canonicity. -/
theorem convergentNormalFormCanStillBeStronglyNormalizing :
    Acc IotaEtaStep.successor
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons (.mkGen .gen_unit () .childNil) .childNil))
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm 0) :=
  IotaEtaStep.isStronglyNormalizing _

end FX1Poly.Core
