import FX1Poly.Core.StratifiedReducibleTypeHeadExpansion
import FX1Poly.Typed.DenoteKeyedReducibility

/-! # FX1Poly/Typed/DenoteKeyedHeadExpansion
    — spine-general head-expansion closure for the denote relation (SN-D1; lambda-arm vehicle toward SN-043/#672)

The fundamental theorem's lambda (Π-introduction) member arm closes — in the fuel/stratified layer — via the
SPINE-GENERAL head-expansion closure `HeadExpansionClosed` (`FX1Poly/Core/HeadExpansionClosure.lean`): the Tait
λ-case `DependentArrowCandidate.abstraction` consumes `HeadExpansionClosed (codomainCandidate argument)`, and the
arrow former preserves the property by ABSORBING the extra application argument into the spine
(`applySpineApp_append`) — so NO SN-of-application and NO `piArm` hypothesis is needed.  This file ports that
closure onto the denote relation `ReducibleTypeStepDenote`, the lower-risk vehicle for the denote lambda arm
(SN-D2) — chosen over discharging the single-`WeakHeadStep` `piArm` of `memberWeakHeadExpansionModuloPi`
directly, which would have to establish the application-SN spine `SN (app source a)` at a function-congruence-of-β
step.

`ReducibleTypeStepDenote.headExpansionClosed` is the verbatim-structured port of
`ReducibleTypeStep.headExpansionClosed` (`StratifiedReducibleTypeHeadExpansion.lean:98`): one induction over the
five `ReducibleTypeStepDenote` arms —
  * `whnfExpand` → the inductive hypothesis (same candidate);
  * `neutral` (SN candidate) → `isStronglyNormalizing_headExpansionClosed`;
  * `piType` (dependent arrow) → `applySpineApp_append` lengthens the spine, discharged by the codomain IH;
  * `universeCode` (`SN ∧ ∃ c, lowerAt (denote levelExpr env) · c`) → SN conjunct by `betaSpineHeadExpansion`,
    the lower conjunct by the `lowerHeadExpand` leg AT THE DECODED LEVEL `LevelExpr.denote levelExpr env`;
  * `ofPointwiseIff` → `HeadExpansionClosed.respectsPointwiseIff`.

`ReducibleTypeAtDenote.headExpansionClosed` discharges the `lowerHeadExpand` leg UNCONDITIONALLY for the real
relation `denoteBelowFamily env level`: it is `denoteBelowFamily_backwardWeakHeadStep` applied to
`WeakHeadStep.betaSpine` (a β-redex at a spine head is a single weak-head step).  Because that backward-step leg
is an implication vacuous on the empty above-bound family (NOT the bounded `neutralInclusion` existence), the
closure is bound-free at every level — no `cases level`/measure needed, unlike the fuel corollary.

## Zero-axiom verification

A structural induction (verbatim port) + a one-line corollary; the universe arm reassembles via the anonymous
constructor (no `funext`), the `ofPointwiseIff` arm transports pointwise.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Spine-general head-expansion closure for the denote relation (parametric).**  Verbatim port of
`ReducibleTypeStep.headExpansionClosed`; the only change is the universe arm's `lowerHeadExpand` leg is taken
at the decoded classifier level `LevelExpr.denote levelExpr env`.  A proof of the leg makes every
denote-reducible candidate head-expansion-closed. -/
theorem ReducibleTypeStepDenote.headExpansionClosed {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (lowerHeadExpand : ∀ (lvl : Nat) {body : RawTerm (scope + 1)} {argument : RawTerm scope}
      {spine : List (RawTerm scope)} {lowerCandidate : RawTerm scope → Prop},
      lowerAt lvl (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) lowerCandidate →
      lowerAt lvl (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons argument .childNil)))
        spine) lowerCandidate)
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    HeadExpansionClosed candidate := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse _notEmpty =>
      exact isStronglyNormalizing_headExpansionClosed
  | @piType _domainCode _codomainCode _domainCandidate codomainCandidate _domainReducible
      _codomainReducible _domainInductiveHypothesis codomainInductiveHypothesis =>
      intro body argument spine argumentSN contractumReducible extraArgument extraArgumentReducible
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
  | universeCode levelExpr _flag =>
      intro _body _argument _spine argumentSN contractumMember
      obtain ⟨contractumStronglyNormalizing, lowerCandidate, lowerContractum⟩ := contractumMember
      exact ⟨betaSpineHeadExpansion argumentSN contractumStronglyNormalizing,
        lowerCandidate, lowerHeadExpand (LevelExpr.denote levelExpr env) lowerContractum⟩
  | dataEmpty =>
      exact emptyTaitCandidate_headExpansionClosed
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis.respectsPointwiseIff (fun term => pointwiseIff term)

/-- **Every denote-reducible candidate at a level is head-expansion-closed (UNCONDITIONAL).**  Discharges the
`lowerHeadExpand` leg for `denoteBelowFamily env level` via `denoteBelowFamily_backwardWeakHeadStep` on
`WeakHeadStep.betaSpine` — bound-free (the backward-step leg is an implication vacuous above the bound), so no
level-case split is needed.  This is the codomain head-expansion closure the denote lambda-arm (SN-D2) feeds to
the generic `DependentArrowCandidate.abstraction`. -/
theorem ReducibleTypeAtDenote.headExpansionClosed {scope : Nat} {env : Nat → Nat} {level : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtDenote env level typeCode candidate) :
    HeadExpansionClosed candidate := by
  refine ReducibleTypeStepDenote.headExpansionClosed ?leg reducible
  intro lvl _body _argument _spine _lowerCandidate contractumMember
  exact denoteBelowFamily_backwardWeakHeadStep env level lvl contractumMember WeakHeadStep.betaSpine

end FX1Poly.Typed
