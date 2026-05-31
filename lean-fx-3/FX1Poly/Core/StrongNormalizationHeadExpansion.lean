import FX1Poly.Core.ReducibilityCandidate
import FX1Poly.Core.ReducibilityCandidateArrow
import FX1Poly.Core.StepInversion
import FX1Poly.Core.StepSubst

/-! # Foundation/PolyCell/Core/StrongNormalizationHeadExpansion
    — β head-expansion for the strong-normalization candidate

The crux closure of the Tait fundamental theorem's λ-abstraction case
(polycell.md §11.8.5): a β-redex `app (lam body) argument` is strongly
normalizing whenever its **contractum** `subst0 body argument` is — given that
both the body and the argument are themselves SN.

## Why this is NOT a corollary of CR3

The shipped reducibility-candidate condition CR3 (`neutralExpansion`) is stated
over *stuck* neutrals (`IsNeutral`: a variable or an elimination with neutral
principal child).  A β-redex `app (lam body) argument` is NOT stuck-neutral —
`lam body` is a constructor, so CR3 does not apply, and head-expansion is NOT
derivable from CR1/CR2/CR3 for a generic candidate.  It IS provable for the
concrete SN candidate, because `IsStronglyNormalizing = Acc StepSuccessor` and
`Acc.intro` is exactly "all reducts are SN ⟹ SN" — the saturation CR3 lacks for
non-neutrals.  Compositional head-expansion (preserved by the arrow/Σ/… formers)
is built on this base case.

## The argument

`Acc.intro` reduces the goal to "every reduct of the redex is SN".  `Step.from_app`
enumerates the three reduct shapes:

* β contraction → `subst0 body argument`, SN by hypothesis (after `cases` on the
  lambda-cell equality identifies the contracted body with `body`);
* head congruence (`body ↝ bodyAfter`) → `app (lam bodyAfter) argument`, by the
  body's `Acc` induction; its contractum `subst0 bodyAfter argument` is SN because
  `subst0 body argument` reaches it (`Step.subst0Body`);
* argument congruence (`argument ↝ argumentAfter`) → `app (lam body) argumentAfter`,
  by the argument's `Acc` induction; its contractum `subst0 body argumentAfter` is
  SN because `subst0 body argument` reaches it (`Step.subst0Argument`).

The two `Acc` inductions nest (argument outer, body inner), and the contractum's
SN is threaded through each, updated along the matching substitution replay.

## Zero-axiom verification

Nested `Acc` induction + `Step.from_app`/`Step.from_lam` inversion + the
`Step.subst0Body`/`Step.subst0Argument` replays + `cases` on the lambda-cell
equality (the propext-safe constructor-injection direction).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept
per declaration by `#audit_namespace FX1Poly.Core` in
`FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- Strong normalization descends along a multi-step reduction: if `source` is
strongly normalizing and `source ↝* target`, then `target` is too.  Iterates the
SN candidate's single-step forward closure (CR2) over the `StepStar` chain. -/
theorem isStronglyNormalizing_of_stepStar {scope : Nat}
    {source target : RawTerm scope} (chain : StepStar source target) :
    IsStronglyNormalizing source → IsStronglyNormalizing target := by
  induction chain with
  | refl _ => exact id
  | trans headStep _tailChain tailInductiveHypothesis =>
      intro sourceStronglyNormalizing
      exact tailInductiveHypothesis
        (isStronglyNormalizing_isReducibilityCandidate.closedUnderStep
          sourceStronglyNormalizing headStep)

/-- **β head-expansion for the SN candidate.**  If the contractum
`subst0 body argument` is strongly normalizing and the body and argument both
are, then the β-redex `app (lam body) argument` is strongly normalizing.  The
λ-abstraction case of the Tait fundamental theorem at base (SN-interpreted)
types. -/
theorem betaRedex_isStronglyNormalizing_of_contractum {scope : Nat}
    {body : RawTerm (scope + 1)} {argument : RawTerm scope}
    (argumentSN : IsStronglyNormalizing argument)
    (bodySN : IsStronglyNormalizing body)
    (contractumSN : IsStronglyNormalizing (RawTerm.subst0 body argument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
          (.childCons argument .childNil))) := by
  suffices general :
      ∀ {currentArgument : RawTerm scope}, Acc StepSuccessor currentArgument →
        ∀ {currentBody : RawTerm (scope + 1)}, Acc StepSuccessor currentBody →
          IsStronglyNormalizing (RawTerm.subst0 currentBody currentArgument) →
          IsStronglyNormalizing
            (.mkGen .gen_app ()
              (.childCons (.mkGen .gen_lam () (.childCons currentBody .childNil))
                (.childCons currentArgument .childNil))) from
    general argumentSN bodySN contractumSN
  intro currentArgument argumentAccessible
  induction argumentAccessible with
  | intro argumentFocus _argumentPredecessors argumentInductiveHypothesis =>
      intro currentBody bodyAccessible
      induction bodyAccessible with
      | intro bodyFocus bodyPredecessorsAccessible bodyInductiveHypothesis =>
          intro currentContractumSN
          apply Acc.intro
          intro reduct reductionStep
          rcases Step.from_app reductionStep with
            ⟨_betaBody, functionEqualsLam, targetEquation⟩ |
            ⟨functionAfter, reductEquation, lambdaStep⟩ |
            ⟨argumentAfter, reductEquation, argumentStep⟩
          · -- β contraction: the contracted body is `bodyFocus`, contractum is SN.
            cases functionEqualsLam
            rw [targetEquation]
            exact currentContractumSN
          · -- head congruence: the lambda body steps `bodyFocus ↝ bodyAfter`.
            obtain ⟨bodyAfter, functionAfterEquation, bodyStep⟩ := Step.from_lam lambdaStep
            rw [reductEquation, functionAfterEquation]
            exact bodyInductiveHypothesis bodyAfter bodyStep
              (isStronglyNormalizing_of_stepStar
                (Step.subst0Body argumentFocus bodyStep) currentContractumSN)
          · -- argument congruence: `argumentFocus ↝ argumentAfter`.
            rw [reductEquation]
            exact argumentInductiveHypothesis argumentAfter argumentStep
              (Acc.intro bodyFocus bodyPredecessorsAccessible)
              (isStronglyNormalizing_of_stepStar
                (Step.subst0Argument bodyFocus argumentStep) currentContractumSN)

/-- Lift a function-position reduction chain to the application: `f ↝* f'` gives
`app f a ↝* app f' a`.  Iterates the head-congruence (`StepChildren.here`). -/
theorem stepStar_appFunction {scope : Nat}
    {function functionReduct : RawTerm scope} (argument : RawTerm scope)
    (chain : StepStar function functionReduct) :
    StepStar
      (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))
      (.mkGen .gen_app ()
        (.childCons functionReduct (.childCons argument .childNil))) := by
  induction chain with
  | refl _ => exact StepStar.refl _
  | trans headStep _tailChain tailInductiveHypothesis =>
      exact StepStar.trans
        (Step.cong .gen_app ()
          (StepChildren.here
            (.childCons argument .childNil : RawTermChildren [0] scope) headStep))
        tailInductiveHypothesis

/-- Lift an argument-position reduction chain to the application: `a ↝* a'` gives
`app f a ↝* app f a'`.  Iterates the tail-then-head congruence
(`StepChildren.there ∘ here`). -/
theorem stepStar_appArgument {scope : Nat} (function : RawTerm scope)
    {argument argumentReduct : RawTerm scope}
    (chain : StepStar argument argumentReduct) :
    StepStar
      (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))
      (.mkGen .gen_app ()
        (.childCons function (.childCons argumentReduct .childNil))) := by
  induction chain with
  | refl _ => exact StepStar.refl _
  | trans headStep _tailChain tailInductiveHypothesis =>
      exact StepStar.trans
        (Step.cong .gen_app ()
          (@StepChildren.there scope 0 [0] function _ _
            (StepChildren.here (.childNil : RawTermChildren [] scope) headStep)))
        tailInductiveHypothesis

/-- **β head-expansion under one application spine.**  If `app (β-contractum) s`
is strongly normalizing — where the β-contractum is `subst0 body argument` — and
`body`, `argument`, `s` are SN, then `app (app (lam body) argument) s` is SN.

This is the head-expansion the Tait fundamental theorem's λ case needs when the
codomain is a (first-order) **arrow** type: there the redex `app (lam body) arg`
sits in the function position of an outer application `· s`, so the spine-free
`betaRedex_isStronglyNormalizing_of_contractum` does not directly apply.  Same
technique, one application deeper: the reduct enumeration uses two `Step.from_app`
inversions (outer, then the head redex), and the contractum's SN is threaded
through the body/argument replays (`Step.subst0Body`/`Step.subst0Argument`, lifted
to the outer application by `stepStar_appFunction`) and the spine replay
(`stepStar_appArgument`).  The arbitrary-spine generalization (for higher-order
codomains) follows the same shape with the spine bounded by the contractum. -/
theorem betaRedexUnderApp_isStronglyNormalizing {scope : Nat}
    {body : RawTerm (scope + 1)} {argument spineArgument : RawTerm scope}
    (argumentSN : IsStronglyNormalizing argument)
    (bodySN : IsStronglyNormalizing body)
    (spineArgumentSN : IsStronglyNormalizing spineArgument)
    (contractumSN :
      IsStronglyNormalizing
        (.mkGen .gen_app ()
          (.childCons (RawTerm.subst0 body argument)
            (.childCons spineArgument .childNil)))) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
              (.childCons argument .childNil)))
          (.childCons spineArgument .childNil))) := by
  suffices general :
      ∀ {currentSpine : RawTerm scope}, Acc StepSuccessor currentSpine →
        ∀ {currentArgument : RawTerm scope}, Acc StepSuccessor currentArgument →
          ∀ {currentBody : RawTerm (scope + 1)}, Acc StepSuccessor currentBody →
            IsStronglyNormalizing
              (.mkGen .gen_app ()
                (.childCons (RawTerm.subst0 currentBody currentArgument)
                  (.childCons currentSpine .childNil))) →
            IsStronglyNormalizing
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app ()
                    (.childCons (.mkGen .gen_lam () (.childCons currentBody .childNil))
                      (.childCons currentArgument .childNil)))
                  (.childCons currentSpine .childNil))) from
    general spineArgumentSN argumentSN bodySN contractumSN
  intro currentSpine spineAccessible
  induction spineAccessible with
  | intro spineFocus spinePredecessorsAccessible spineInductiveHypothesis =>
      intro currentArgument argumentAccessible
      induction argumentAccessible with
      | intro argumentFocus argumentPredecessorsAccessible argumentInductiveHypothesis =>
          intro currentBody bodyAccessible
          induction bodyAccessible with
          | intro bodyFocus bodyPredecessorsAccessible bodyInductiveHypothesis =>
              intro currentContractumSN
              apply Acc.intro
              intro reduct outerReductionStep
              rcases Step.from_app outerReductionStep with
                ⟨_outerBetaBody, headEqualsLam, _⟩ |
                ⟨headReduct, reductEquation, headStep⟩ |
                ⟨spineReduct, reductEquation, spineStep⟩
              · -- outer β impossible: the function `app (lam …) …` is not a λ.
                exact Generator.noConfusion
                  (congrArg RawTerm.rootGenerator headEqualsLam)
              · -- head reduction: invert the head redex `app (lam bodyFocus) argumentFocus`.
                rcases Step.from_app headStep with
                  ⟨innerBetaBody, lambdaEquation, headReductEquation⟩ |
                  ⟨lambdaReduct, headReductEquation, lambdaStep⟩ |
                  ⟨argumentReduct, headReductEquation, argumentStep⟩
                · -- inner β: the reduct is the contractum under the spine.
                  cases lambdaEquation
                  rw [reductEquation, headReductEquation]
                  exact currentContractumSN
                · -- inner body congruence: `bodyFocus ↝ bodyAfter`.
                  obtain ⟨bodyAfter, lambdaReductEquation, bodyStep⟩ :=
                    Step.from_lam lambdaStep
                  rw [reductEquation, headReductEquation, lambdaReductEquation]
                  exact bodyInductiveHypothesis bodyAfter bodyStep
                    (isStronglyNormalizing_of_stepStar
                      (stepStar_appFunction spineFocus
                        (Step.subst0Body argumentFocus bodyStep))
                      currentContractumSN)
                · -- inner argument congruence: `argumentFocus ↝ argumentReduct`.
                  rw [reductEquation, headReductEquation]
                  exact argumentInductiveHypothesis argumentReduct argumentStep
                    (Acc.intro bodyFocus bodyPredecessorsAccessible)
                    (isStronglyNormalizing_of_stepStar
                      (stepStar_appFunction spineFocus
                        (Step.subst0Argument bodyFocus argumentStep))
                      currentContractumSN)
              · -- spine congruence: `spineFocus ↝ spineReduct`.
                rw [reductEquation]
                exact spineInductiveHypothesis spineReduct spineStep
                  (Acc.intro argumentFocus argumentPredecessorsAccessible)
                  (Acc.intro bodyFocus bodyPredecessorsAccessible)
                  (isStronglyNormalizing_of_stepStar
                    (stepStar_appArgument (RawTerm.subst0 bodyFocus argumentFocus)
                      (StepStar.single spineStep))
                    currentContractumSN)

end StepStar
end FX1Poly.Core
