import FX1Poly.Core.StratifiedReducibleTypeReducibilityCandidate
import FX1Poly.Core.HeadExpansionClosure

/-! # Foundation/PolyCell/Core/StratifiedReducibleTypeHeadExpansion
    — every stratified-reducible type's candidate is head-expansion-closed

The stratified port of `ReducibleType.headExpansionClosed`, the prerequisite for the fundamental theorem's
Π-introduction (`abstraction`) rule: a λ is a member of the dependent arrow because, for every reducible
argument, the β-redex `app (lam body) argument` inherits its codomain membership from the contractum
`subst0 body argument` — i.e. each interpreted candidate is closed under β-head-expansion at a spine head.

The three non-universe arms mirror the pure-SN proof (`whnfExpand` → induction hypothesis, `neutral` → the
SN candidate's `isStronglyNormalizing_headExpansionClosed`, `piType` → the dependent-arrow closure via
`applySpineApp_append`).  The NEW `universeCode` arm needs its candidate `universeReducibilityPredicate low`
= `SN tc ∧ ∃c, low tc c` head-expansion-closed: the SN conjunct by `betaSpineHeadExpansion`, the
reducible-type conjunct by the lower relation's OWN β-spine backward closure (the interface hypothesis
`lowerHeadExpand`).

## The β-spine substrate

`lowerHeadExpand` is discharged for the tower by two reusable bricks shipped here:

  * `WeakHeadStep.applySpine` — a head weak-head-step lifts through an application spine (each spine element
    absorbed by `appCongruence`); hence `WeakHeadStep.betaSpine` — a β-redex at a spine head IS a weak-head
    step (`applySpine` of `WeakHeadStep.beta`).
  * `ReducibleTypeStep/At.headExpand` — a reducible type is backward-closed under one weak-head step (the
    `whnfExpand` constructor; the level version by `cases level`).

Together: `ReducibleTypeAt.headExpand WeakHeadStep.betaSpine` is exactly the type-level β-spine backward
closure the universe arm's interface demands, so `ReducibleTypeAt.headExpansionClosed` is UNCONDITIONAL.

## Zero-axiom verification

Spine induction (`applySpine`) + the `whnfExpand` constructor (`headExpand`) + `induction reducible` over the
four arms (`applySpineApp_append` `rw` for `piType`, `betaSpineHeadExpansion` + `lowerHeadExpand` for
`universeCode`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **A head weak-head-step lifts through an application spine.**  If the head weak-head-steps, the whole
spined application weak-head-steps at the head — each spine element absorbed by `appCongruence`.  Spine
induction: the cons step augments the head with the leading argument and recurses. -/
theorem WeakHeadStep.applySpine {scope : Nat} :
    ∀ (spine : List (RawTerm scope)) {head headReduct : RawTerm scope},
      WeakHeadStep head headReduct →
      WeakHeadStep (RawTerm.applySpineApp head spine) (RawTerm.applySpineApp headReduct spine) := by
  intro spine
  induction spine with
  | nil => intro _head _headReduct headStep; exact headStep
  | cons _spineElement _restSpine restInductiveHypothesis =>
      intro _head _headReduct headStep
      exact restInductiveHypothesis (WeakHeadStep.appCongruence headStep)

/-- **A β-redex at a spine head is a weak-head step.**  `WeakHeadStep.applySpine` of `WeakHeadStep.beta`:
`applySpineApp (app (lam body) argument) spine` weak-head-reduces to `applySpineApp (subst0 body argument)
spine`. -/
theorem WeakHeadStep.betaSpine {scope : Nat} {body : RawTerm (scope + 1)}
    {argument : RawTerm scope} {spine : List (RawTerm scope)} :
    WeakHeadStep
      (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons argument .childNil)))
        spine)
      (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) :=
  WeakHeadStep.applySpine spine WeakHeadStep.beta

/-- **A stratified reducible type is backward-closed under one weak-head step** — literally the `whnfExpand`
constructor (a reduct's candidate is the redex's). -/
theorem ReducibleTypeStep.headExpand {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (weakHeadStep : WeakHeadStep typeCode reduct)
    (reductReducible : ReducibleTypeStep lowerReducible reduct candidate) :
    ReducibleTypeStep lowerReducible typeCode candidate :=
  ReducibleTypeStep.whnfExpand weakHeadStep reductReducible

/-- **Backward closure under one weak-head step, level-indexed.**  `headExpand` through the `Nat` recursion
(both cases by defeq). -/
theorem ReducibleTypeAt.headExpand {scope : Nat} {level : Nat}
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (weakHeadStep : WeakHeadStep typeCode reduct)
    (reductReducible : ReducibleTypeAt level reduct candidate) :
    ReducibleTypeAt level typeCode candidate := by
  cases level with
  | zero => exact ReducibleTypeStep.headExpand weakHeadStep reductReducible
  | succ predLevel => exact ReducibleTypeStep.headExpand weakHeadStep reductReducible

/-- **Every stratified-reducibility candidate is head-expansion-closed** (parametric).  By induction on the
derivation: `whnfExpand` reuses the induction hypothesis, `neutral` is the SN candidate, `piType` is the
dependent-arrow closure (`applySpineApp_append`), and `universeCode`'s candidate `SN ∧ ∃c, low tc c` is
closed conjunct-wise — SN by `betaSpineHeadExpansion`, the reducible-type conjunct by the lower relation's
β-spine backward closure (`lowerHeadExpand`). -/
theorem ReducibleTypeStep.headExpansionClosed {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    (lowerHeadExpand : ∀ {body : RawTerm (scope + 1)} {argument : RawTerm scope}
      {spine : List (RawTerm scope)} {lowerCandidate : RawTerm scope → Prop},
      lowerReducible (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) lowerCandidate →
      lowerReducible (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons argument .childNil)))
        spine) lowerCandidate)
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStep lowerReducible typeCode candidate) :
    HeadExpansionClosed candidate := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse =>
      exact isStronglyNormalizing_headExpansionClosed
  | piType codomainCandidate _domainReducible _codomainReducible
      _domainInductiveHypothesis codomainInductiveHypothesis =>
      intro body argument spine argumentSN contractumReducible
      intro extraArgument extraArgumentReducible
      have contractumAtExtendedSpine :
          codomainCandidate extraArgument
            (RawTerm.applySpineApp (RawTerm.subst0 body argument) (spine ++ [extraArgument])) := by
        rw [applySpineApp_append]
        exact contractumReducible extraArgument extraArgumentReducible
      have redexAtExtendedSpine :
          codomainCandidate extraArgument
            (RawTerm.applySpineApp
              (.mkGen .gen_app ()
                (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
                  (.childCons argument .childNil)))
              (spine ++ [extraArgument])) :=
        (codomainInductiveHypothesis extraArgument extraArgumentReducible)
          argumentSN contractumAtExtendedSpine
      rw [applySpineApp_append] at redexAtExtendedSpine
      exact redexAtExtendedSpine
  | universeCode _levelExpr _flag =>
      intro _body _argument _spine argumentSN contractumMember
      obtain ⟨contractumStronglyNormalizing, lowerCandidate, lowerContractum⟩ := contractumMember
      exact ⟨betaSpineHeadExpansion argumentSN contractumStronglyNormalizing,
        lowerCandidate, lowerHeadExpand lowerContractum⟩
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis.respectsPointwiseIff (fun term => pointwiseIff term)

/-- **Every level-indexed reducibility candidate is head-expansion-closed** (unconditional).
`ReducibleTypeStep.headExpansionClosed` with `lowerHeadExpand` discharged: at level `0` the lower relation
is empty (`False`-closure trivial); at `predLevel + 1` it is `ReducibleTypeAt.headExpand WeakHeadStep.betaSpine`
(a reducible type backward-closes under the β-spine weak-head step). -/
theorem ReducibleTypeAt.headExpansionClosed {scope : Nat} {level : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAt level typeCode candidate) :
    HeadExpansionClosed candidate := by
  cases level with
  | zero =>
      exact ReducibleTypeStep.headExpansionClosed
        (fun lowerContractum => lowerContractum.elim) reducible
  | succ predLevel =>
      exact ReducibleTypeStep.headExpansionClosed
        (fun lowerContractum => ReducibleTypeAt.headExpand WeakHeadStep.betaSpine lowerContractum)
        reducible

end FX1Poly.Core
