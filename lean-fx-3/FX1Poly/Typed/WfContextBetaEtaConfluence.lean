import FX1Poly.Typed.OpenStronglyNormalizingBetaEta
import FX1Poly.Core.StepBetaEtaConfluence

/-! # FX1Poly/Typed/WfContextBetaEtaConfluence
    — harvesting OSN-1: βη Church-Rosser + unique βη-normal-forms on the WfContext fragment (OSN-B8)

This is the βη (really βιη) twin of `WfContextDecidableConv.subjectConfluenceOfWfContext` (the β/ι harvest of
open SN-043).  It ships the **Geuvers theorem**: Church-Rosser for βη holds on the WELL-TYPED terms — exactly
what OSN-1 (`HasTypeDescPi.betaEtaStronglyNormalizingOfWfContext`, βη-SN for well-typed terms in a well-formed
context) now makes available.

## Why the restriction to well-typed terms is the honest, MAXIMAL statement

RAW βη Church-Rosser is FALSE: Nederpelt (1973) exhibits a non-confluent βη overlap
`λx:σ.(λy:τ.M)x` (`x ∉ FV M`), resolvable only when typing forces `σ = τ`; and Klop (1980) shows β + surjective
pairing (FX's `etaPair`) is globally non-confluent on raw terms.  Geuvers (LICS '92, *The Church-Rosser
Property for βη-reduction in Typed λ-Calculi*) proves CR for βη on the well-typed terms of a fixed type is
"the maximum one can expect."  FX's `subjectBetaEtaConfluenceOfWfContext` is the constructive form of that
theorem, factored cleanly: raw LOCAL βη-confluence (`cd_lemma_betaEta`, holds for ALL terms — consistent with
Klop, since local ≠ global) ⊕ TYPED βη-SN (OSN-1) → typed global CR, by Newman
(`Step.betaEtaStar.confluence_of_localJoin_and_accessible`).  Typing is load-bearing only through SN; raw
global confluence (false) is never used.

## What is shipped vs deferred

  * `Step.betaEtaStar.eq_of_noBetaEtaStep` — βη star-rigidity: a βη-star chain out of a term with no βη-step
    is trivial (the endpoint IS the start).  Pure raw-reduction lemma.
  * `HasTypeDescPi.subjectBetaEtaConfluenceOfWfContext` — the Geuvers βη-CR: any two βη-reducts of a well-typed
    subject in a well-formed context join.
  * `HasTypeDescPi.uniqueBetaEtaNormalFormOfWfContext` — the standard CR consequence: a well-typed subject has
    at most one βη-normal-form (two βη-NFs reached from it are equal), via CR + star-rigidity.

DEFERRED to the Path-A βη normalizer (a βη analogue of the WN-grind spine): WEAK βη-normalization (EXISTENCE
of a βη-NF) and DECIDABLE βη-Conv.  Existence/decidability need a computable βη-redex-firing normalizer, which
does not yet exist; the modern route for η-bearing conversion is type-directed NbE / logical relations
(Abel-Öhman-Vezzosi POPL '18), tracked separately.  This file does NOT fake them from confluence alone.

## Zero-axiom verification

`eq_of_noBetaEtaStep` is a two-case `cases` on `betaEtaStar` (free-index unification, propext-clean); the two
typed results are one-line compositions of OSN-1 with the shipped βη-Newman bridge.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated.
-/

namespace FX1Poly.Core

/-- **βη star-rigidity.**  If `startTerm` admits no `Step.betaEta` step, then any `Step.betaEtaStar` chain out
of it is trivial — the endpoint equals the start.  (A βη-normal-form reached by a βη-star reduction was the
reduction's own source.)  By cases on the closure: the left-extension constructor would supply a βη-step out
of `startTerm`, contradicting the hypothesis. -/
theorem Step.betaEtaStar.eq_of_noBetaEtaStep {scope : Nat} {startTerm endTerm : RawTerm scope}
    (noStep : ∀ reduct : RawTerm scope, ¬ Step.betaEta startTerm reduct)
    (chain : Step.betaEtaStar startTerm endTerm) :
    startTerm = endTerm := by
  cases chain with
  | refl => rfl
  | trans firstStep _ => exact absurd firstStep (noStep _)

end FX1Poly.Core

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **βη Church-Rosser on the WfContext fragment — the Geuvers theorem (OSN-B8).**  Any two βη-reducts of a
well-typed subject in a well-formed context join.  Per-source Newman
(`Step.betaEtaStar.confluence_of_localJoin_and_accessible`, raw local βη-confluence baked in) fed the
subject's OSN-1 βη-SN witness (`betaEtaStronglyNormalizingOfWfContext`).  The βη twin of the β/ι
`subjectConfluenceOfWfContext`; raw global βη-confluence (false by Nederpelt/Klop) is never used. -/
theorem HasTypeDescPi.subjectBetaEtaConfluenceOfWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftReduct rightReduct : RawTerm scope}
    (subjectToLeft : Step.betaEtaStar subject leftReduct)
    (subjectToRight : Step.betaEtaStar subject rightReduct) :
    Step.betaEtaStar.Join leftReduct rightReduct :=
  Step.betaEtaStar.confluence_of_localJoin_and_accessible
    (HasTypeDescPi.betaEtaStronglyNormalizingOfWfContext contextWellFormed typed)
    subjectToLeft subjectToRight

/-- **Unique βη-normal-forms on the WfContext fragment.**  A well-typed subject in a well-formed context has
at most one βη-normal-form: if it βη-reduces to two terms each admitting no further βη-step, those terms are
equal.  The standard Church-Rosser consequence — `subjectBetaEtaConfluenceOfWfContext` produces a common
βη-reduct (apex), and `Step.betaEtaStar.eq_of_noBetaEtaStep` collapses each normal form onto that apex.  The
βη twin of `uniqueNormalFormOfWfContext` (existence/weak-normalization is the deferred normalizer half). -/
theorem HasTypeDescPi.uniqueBetaEtaNormalFormOfWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier)
    {normalFormLeft normalFormRight : RawTerm scope}
    (subjectToLeft : Step.betaEtaStar subject normalFormLeft)
    (leftNoStep : ∀ reduct : RawTerm scope, ¬ Step.betaEta normalFormLeft reduct)
    (subjectToRight : Step.betaEtaStar subject normalFormRight)
    (rightNoStep : ∀ reduct : RawTerm scope, ¬ Step.betaEta normalFormRight reduct) :
    normalFormLeft = normalFormRight := by
  obtain ⟨apex, leftToApex, rightToApex⟩ :=
    HasTypeDescPi.subjectBetaEtaConfluenceOfWfContext contextWellFormed typed subjectToLeft subjectToRight
  have leftEqApex : normalFormLeft = apex := Step.betaEtaStar.eq_of_noBetaEtaStep leftNoStep leftToApex
  have rightEqApex : normalFormRight = apex := Step.betaEtaStar.eq_of_noBetaEtaStep rightNoStep rightToApex
  exact leftEqApex.trans rightEqApex.symm

end FX1Poly.Typed
