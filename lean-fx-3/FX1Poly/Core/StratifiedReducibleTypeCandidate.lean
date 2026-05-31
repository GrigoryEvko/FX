import FX1Poly.Core.StratifiedReducibleTypeForwardClosure
import FX1Poly.Core.ReducibilityCandidate

/-! # Foundation/PolyCell/Core/StratifiedReducibleTypeCandidate
    — the Tarski-universe candidate is a genuine Girard reducibility candidate

This file closes the soundness question for the stratified Tarski universe: the universe code's candidate
`universeReducibilityPredicate lowerReducible` (a type code is in the universe when it is strongly
normalizing AND is a reducible type at the lower level) satisfies all three Girard CR conditions, so the
universe is a legitimate reducibility candidate — the precondition for the fundamental theorem's universe /
type-variable handling.

## Why the SN conjunct (the latent CR1 flaw it repairs)

The earlier formulation made a universe code denote the BARE predicate `∃ c, lowerReducible tc c` ("tc is a
reducible type").  That FAILS CR1.  The `neutral` arm of `ReducibleTypeStep` admits non-SN reducible types:
`app (var f) omega` is weak-head-normal (the variable head blocks every weak-head redex), non-Pi,
non-universe — hence a reducible type — yet it loops on its argument `omega`, so it is NOT strongly
normalizing.  The bare predicate would therefore contain non-SN members and break "every reducible term is
SN".  Conjoining `IsStronglyNormalizing` (in `universeReducibilityPredicate`) FILTERS those junk types out:
CR1 now reads straight off the conjunct, and — bonus — a reducible environment at a type variable now
carries BOTH the variable's SN witness and its candidate, which is exactly what the fundamental theorem's
conversion arm consumes.

## The type-level interface

CR2 and CR3 of the universe candidate are not unconditional: they delegate to the lower relation's
TYPE-LEVEL behaviour, captured as two honest hypotheses on `lowerReducible`:

  * `lowerForwardStep` — reducible types are forward-closed under one `Step` (drives CR2's second conjunct).
  * `lowerNeutralInclusion` — a neutral type all of whose reducts are reducible types is itself a reducible
    type (drives CR3's second conjunct).

CR1 needs neither; CR2/CR3's SN conjuncts are pure `Acc` manipulation (mirroring
`isStronglyNormalizing_isReducibilityCandidate`).  The forward leg is DISCHARGED here for the step relation
(`ReducibleTypeStep.forwardStep`, a single-step specialization of `forwardStepStar`); the neutral leg's
descent needs "neutrals are weak-head-normal" and lands in a later brick.

## Zero-axiom verification

`refine ⟨…⟩` over the three CR fields: CR1 is a projection, CR2 is `Acc` inversion plus `lowerForwardStep`,
CR3 is `Acc.intro` plus `lowerNeutralInclusion`.  The forward leg is `forwardStepStar` ∘ `StepStar.single`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration
by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Single-step type-level forward closure.**  A stratified reducible type stays reducible at the same
candidate under one `Step` — `forwardStepStar` specialized to a one-step chain (`StepStar.single`).  This
is precisely the `lowerForwardStep` interface hypothesis at the step relation: it DISCHARGES that leg for
`ReducibleTypeStep lowerReducible` (and, via the level wrapper below, for every `ReducibleTypeAt`). -/
theorem ReducibleTypeStep.forwardStep {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStep lowerReducible typeCode candidate)
    (step : Step typeCode reduct) :
    ReducibleTypeStep lowerReducible reduct candidate :=
  ReducibleTypeStep.forwardStepStar reducible (StepStar.single step)

/-- **Single-step type-level forward closure, level-indexed.**  `ReducibleTypeStep.forwardStep` through the
`Nat` recursion of `ReducibleTypeAt` (both cases by defeq).  Explicit `ReducibleTypeStep.forwardStep`
avoids a self-recursive resolution to `ReducibleTypeAt.forwardStep`. -/
theorem ReducibleTypeAt.forwardStep {scope : Nat} {level : Nat}
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAt level typeCode candidate)
    (step : Step typeCode reduct) :
    ReducibleTypeAt level reduct candidate := by
  cases level with
  | zero => exact ReducibleTypeStep.forwardStep reducible step
  | succ predLevel => exact ReducibleTypeStep.forwardStep reducible step

/-- **The Tarski-universe candidate is a Girard reducibility candidate.**  Given that the lower relation is
forward-step-closed (`lowerForwardStep`) and neutral-closed (`lowerNeutralInclusion`) at the type level,
`universeReducibilityPredicate lowerReducible` satisfies all three CR conditions:

  * CR1 (members are SN): read off the `IsStronglyNormalizing` conjunct — the repair the SN conjunct exists
    for (a bare "is a reducible type" predicate fails here on junk like `app (var f) omega`).
  * CR2 (forward step-closure): the SN conjunct is closed by one-step `Acc` inversion; the reducible-type
    conjunct by `lowerForwardStep`.
  * CR3 (neutral expansion): the SN conjunct is `Acc.intro` over the neutral term's reducts; the
    reducible-type conjunct by `lowerNeutralInclusion`.

This makes the stratified universe a legitimate candidate — the precondition for interpreting a universe
code (and hence every type variable typed by it) in the fundamental theorem. -/
theorem ReducibleTypeStep.universeCandidateIsReducibilityCandidate {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    (lowerForwardStep : ∀ {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop},
      lowerReducible typeCode candidate → Step typeCode reduct → lowerReducible reduct candidate)
    (lowerNeutralInclusion : ∀ {typeCode : RawTerm scope}, IsNeutral typeCode →
      (∀ reduct : RawTerm scope, Step typeCode reduct →
        ∃ candidate : RawTerm scope → Prop, lowerReducible reduct candidate) →
      ∃ candidate : RawTerm scope → Prop, lowerReducible typeCode candidate) :
    IsReducibilityCandidate (universeReducibilityPredicate lowerReducible) := by
  refine ⟨?stronglyNormalizing, ?closedUnderStep, ?neutralExpansion⟩
  case stronglyNormalizing =>
    intro typeCode member
    obtain ⟨memberStronglyNormalizing, _memberReducibleType⟩ := member
    exact memberStronglyNormalizing
  case closedUnderStep =>
    intro typeCode reduct member step
    obtain ⟨memberStronglyNormalizing, lowerCandidate, lowerTypeCode⟩ := member
    refine ⟨?reductStronglyNormalizing, lowerCandidate, lowerForwardStep lowerTypeCode step⟩
    cases memberStronglyNormalizing with
    | intro _typeCode predecessorsAccessible => exact predecessorsAccessible reduct step
  case neutralExpansion =>
    intro typeCode typeCodeIsNeutral reductsMember
    refine ⟨Acc.intro typeCode (fun reduct step => (reductsMember reduct step).1), ?reducibleType⟩
    exact lowerNeutralInclusion typeCodeIsNeutral
      (fun reduct step => (reductsMember reduct step).2)

end FX1Poly.Core
