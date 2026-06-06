import FX1Poly.Core.ReducibilityCandidate
import FX1Poly.Core.ReducibilityCandidateArrow
import FX1Poly.Core.StepInversion
import FX1Poly.Core.StepSubst

/-! # Foundation/PolyCell/Core/StrongNormalizationSpineExpansion
    — β head-expansion under an ARBITRARY application spine (the general theorem)

This SUBSUMES the spine-length staircase (`betaRedex_…_of_contractum` = empty spine,
`betaRedexUnderApp_…` = singleton spine) with ONE theorem parameterised by the spine
list, so the head-expansion does not grow one lemma per function order.

`applySpineApp head [s₁,…,sₙ] = (… ((head s₁) s₂) …) sₙ` is the standard left-nested
application spine.  The general head-expansion is

  `betaSpineHeadExpansion : SN argument → SN (applySpineApp (subst0 body argument) spine)
                              → SN (applySpineApp (app (lam body) argument) spine)`

— note only TWO hypotheses: the contractum's SN bounds both the body (every body step
shows up in the contractum via `subst0Body`) and the spine (every spine step shows up
directly), so only the argument needs its own measure (a `subst0Argument` step can be
empty when the bound variable is absent from the body).

## Genericity note

`applySpineApp` is the application-only spine — the only elimination form in the grown
engine.  When ι-eliminators land, the spine generalises to a stack of elimination
frames (one frame former per eliminator, the SAME proof) — this file is structured so
that generalisation is additive, not a rewrite.

## Zero-axiom verification

`Step.from_applySpineApp` inversion + nested `Acc` induction + the `applySpineApp`
congruence lifts.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- Strong normalization descends along a multi-step reduction: if `source` is strongly
normalizing and `source ↝* target`, then `target` is too.  Iterates the SN candidate's
single-step forward closure (CR2) over the `StepStar` chain. -/
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

/-- Left-nested application spine: `applySpineApp head [s₁,…,sₙ] = head s₁ s₂ … sₙ`. -/
def RawTerm.applySpineApp {scope : Nat} (head : RawTerm scope) :
    List (RawTerm scope) → RawTerm scope
  | [] => head
  | spineElement :: restSpine =>
      RawTerm.applySpineApp
        (.mkGen .gen_app () (.childCons head (.childCons spineElement .childNil)))
        restSpine

/-- One spine element steps — the reduction relation on application spines. -/
inductive SpineStep {scope : Nat} :
    List (RawTerm scope) → List (RawTerm scope) → Prop where
  | head {spineElement updatedElement : RawTerm scope}
      {restSpine : List (RawTerm scope)} (elementStep : Step spineElement updatedElement) :
      SpineStep (spineElement :: restSpine) (updatedElement :: restSpine)
  | tail {spineElement : RawTerm scope}
      {restSpine updatedRest : List (RawTerm scope)} (restStep : SpineStep restSpine updatedRest) :
      SpineStep (spineElement :: restSpine) (spineElement :: updatedRest)

/-- A head step lifts to the spined application: `head ↝ head'` gives
`applySpineApp head spine ↝ applySpineApp head' spine` (head-congruence at every level). -/
theorem Step.applySpineAppHead {scope : Nat} (spine : List (RawTerm scope)) :
    ∀ {head updatedHead : RawTerm scope}, Step head updatedHead →
      Step (RawTerm.applySpineApp head spine) (RawTerm.applySpineApp updatedHead spine) := by
  induction spine with
  | nil => intro _head _updatedHead headStep; exact headStep
  | cons spineElement restSpine restInductiveHypothesis =>
      intro head updatedHead headStep
      exact restInductiveHypothesis
        (Step.cong .gen_app ()
          (StepChildren.here
            (.childCons spineElement .childNil : RawTermChildren [0] scope) headStep))

/-- A head reduction chain lifts to the spined application. -/
theorem StepStar.applySpineAppHead {scope : Nat} (spine : List (RawTerm scope))
    {head updatedHead : RawTerm scope} (chain : StepStar head updatedHead) :
    StepStar (RawTerm.applySpineApp head spine) (RawTerm.applySpineApp updatedHead spine) := by
  induction chain with
  | refl _ => exact StepStar.refl _
  | trans headStep _tailChain tailInductiveHypothesis =>
      exact StepStar.trans (Step.applySpineAppHead spine headStep) tailInductiveHypothesis

/-- A spine step lifts to the spined application: one element of the spine steps gives one
step of the whole application. -/
theorem Step.applySpineAppSpine {scope : Nat}
    {spine updatedSpine : List (RawTerm scope)} (spineStep : SpineStep spine updatedSpine) :
    ∀ head : RawTerm scope,
      Step (RawTerm.applySpineApp head spine) (RawTerm.applySpineApp head updatedSpine) := by
  induction spineStep with
  | head elementStep =>
      intro head
      exact Step.applySpineAppHead _
        (Step.cong .gen_app ()
          (@StepChildren.there scope 0 [0] head _ _
            (StepChildren.here (.childNil : RawTermChildren [] scope) elementStep)))
  | tail _restStep restInductiveHypothesis =>
      intro head
      exact restInductiveHypothesis
        (.mkGen .gen_app () (.childCons head (.childCons _ .childNil)))

/-- **Inversion for a step out of a spined application** (with a non-λ head): every reduct
of `applySpineApp head spine` either steps the head or steps one spine element. -/
theorem Step.from_applySpineApp {scope : Nat} :
    ∀ {spine : List (RawTerm scope)} {head reduct : RawTerm scope},
      RawTerm.rootGenerator head ≠ Generator.gen_lam →
      Step (RawTerm.applySpineApp head spine) reduct →
      (∃ headReduct, Step head headReduct ∧ reduct = RawTerm.applySpineApp headReduct spine) ∨
      (∃ updatedSpine, SpineStep spine updatedSpine ∧
        reduct = RawTerm.applySpineApp head updatedSpine) := by
  intro spine
  induction spine with
  | nil =>
      intro head reduct _headNotLam stepReduct
      exact Or.inl ⟨reduct, stepReduct, rfl⟩
  | cons spineElement restSpine restInductiveHypothesis =>
      intro head reduct _headNotLam stepReduct
      have wrappedHeadNotLam :
          RawTerm.rootGenerator
              (.mkGen .gen_app () (.childCons head (.childCons spineElement .childNil)))
            ≠ Generator.gen_lam :=
        fun wrappedEquation => Generator.noConfusion wrappedEquation
      rcases restInductiveHypothesis wrappedHeadNotLam stepReduct with
        ⟨wrappedReduct, wrappedStep, reductEquation⟩ |
        ⟨updatedRest, restSpineStep, reductEquation⟩
      · rcases Step.from_app wrappedStep with
          ⟨_betaBody, headEqualsLam, _⟩ |
          ⟨headReduct, wrappedReductEquation, headStep⟩ |
          ⟨elementReduct, wrappedReductEquation, elementStep⟩
        · exact absurd (congrArg RawTerm.rootGenerator headEqualsLam) _headNotLam
        · exact Or.inl ⟨headReduct, headStep,
            reductEquation.trans
              (congrArg (fun functionHead => RawTerm.applySpineApp functionHead restSpine)
                wrappedReductEquation)⟩
        · exact Or.inr ⟨elementReduct :: restSpine, SpineStep.head elementStep,
            reductEquation.trans
              (congrArg (fun functionHead => RawTerm.applySpineApp functionHead restSpine)
                wrappedReductEquation)⟩
      · exact Or.inr ⟨spineElement :: updatedRest, SpineStep.tail restSpineStep, reductEquation⟩

/-- **β head-expansion under an arbitrary application spine** — the single theorem that
subsumes the spine-length staircase (`betaRedex_…_of_contractum`, `betaRedexUnderApp_…`).
If the argument is SN and the spined contractum `applySpineApp (subst0 body argument) spine`
is SN, then the spined β-redex `applySpineApp (app (lam body) argument) spine` is SN.

Two hypotheses suffice: the contractum's accessibility bounds every body reduction (via
`subst0Body`, lifted by `applySpineAppHead`) and every spine reduction (the spine elements
appear directly in the contractum); only the argument needs its own measure (a
`subst0Argument` replay can be empty when the bound variable is absent from the body).  The
induction is therefore nested `Acc` on `(argument, contractum)`, with `(body, spine)`
generalised and linked to the contractum by an equation. -/
theorem betaSpineHeadExpansion {scope : Nat}
    {body : RawTerm (scope + 1)} {argument : RawTerm scope}
    {spine : List (RawTerm scope)}
    (argumentSN : IsStronglyNormalizing argument)
    (contractumSN :
      IsStronglyNormalizing
        (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine)) :
    IsStronglyNormalizing
      (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons argument .childNil)))
        spine) := by
  suffices general :
      ∀ {currentArgument : RawTerm scope}, Acc StepSuccessor currentArgument →
        ∀ {currentContractum : RawTerm scope}, Acc StepSuccessor currentContractum →
          ∀ (currentBody : RawTerm (scope + 1)) (currentSpine : List (RawTerm scope)),
            currentContractum =
              RawTerm.applySpineApp (RawTerm.subst0 currentBody currentArgument) currentSpine →
            IsStronglyNormalizing
              (RawTerm.applySpineApp
                (.mkGen .gen_app ()
                  (.childCons (.mkGen .gen_lam () (.childCons currentBody .childNil))
                    (.childCons currentArgument .childNil)))
                currentSpine) from
    general argumentSN contractumSN body spine rfl
  intro currentArgument argumentAccessible
  induction argumentAccessible with
  | intro argumentFocus _argumentPredecessors argumentInductiveHypothesis =>
      intro currentContractum contractumAccessible
      induction contractumAccessible with
      | intro contractumFocus contractumPredecessorsAccessible contractumInductiveHypothesis =>
          intro currentBody currentSpine contractumEquation
          apply Acc.intro
          intro reduct reductionStep
          have headNotLam :
              RawTerm.rootGenerator
                  (.mkGen .gen_app ()
                    (.childCons (.mkGen .gen_lam () (.childCons currentBody .childNil))
                      (.childCons argumentFocus .childNil)))
                ≠ Generator.gen_lam :=
            fun headEquation => Generator.noConfusion headEquation
          rcases Step.from_applySpineApp headNotLam reductionStep with
            ⟨headReduct, headStep, reductEquation⟩ |
            ⟨updatedSpine, spineStep, reductEquation⟩
          · rcases Step.from_app headStep with
              ⟨_betaBody, lambdaEquation, headReductEquation⟩ |
              ⟨lambdaReduct, headReductEquation, lambdaStep⟩ |
              ⟨argumentReduct, headReductEquation, argumentStep⟩
            · -- β contraction: the reduct is exactly the contractum.
              cases lambdaEquation
              rw [reductEquation, headReductEquation, ← contractumEquation]
              exact Acc.intro contractumFocus contractumPredecessorsAccessible
            · -- inner body congruence: `currentBody ↝ bodyAfter`.
              obtain ⟨bodyAfter, lambdaReductEquation, bodyStep⟩ := Step.from_lam lambdaStep
              rw [reductEquation, headReductEquation, lambdaReductEquation]
              refine contractumInductiveHypothesis
                (RawTerm.applySpineApp (RawTerm.subst0 bodyAfter argumentFocus) currentSpine)
                ?_ bodyAfter currentSpine rfl
              rw [contractumEquation]
              exact Step.applySpineAppHead currentSpine
                (Step.subst (RawTermSubst.singleton argumentFocus) bodyStep)
            · -- inner argument congruence: `argumentFocus ↝ argumentReduct`.
              rw [reductEquation, headReductEquation]
              refine argumentInductiveHypothesis argumentReduct argumentStep
                (isStronglyNormalizing_of_stepStar
                  (by rw [contractumEquation]
                      exact StepStar.applySpineAppHead currentSpine
                        (Step.subst0Argument currentBody argumentStep))
                  (Acc.intro contractumFocus contractumPredecessorsAccessible))
                currentBody currentSpine rfl
          · -- spine congruence: one spine element steps.
            rw [reductEquation]
            refine contractumInductiveHypothesis
              (RawTerm.applySpineApp (RawTerm.subst0 currentBody argumentFocus) updatedSpine)
              ?_ currentBody updatedSpine rfl
            rw [contractumEquation]
            exact Step.applySpineAppSpine spineStep (RawTerm.subst0 currentBody argumentFocus)

/-- **β head-expansion, spine-free** — the common base case: the empty-spine instance of
`betaSpineHeadExpansion`.  If the argument is SN and the contractum `subst0 body argument` is
SN, then `app (lam body) argument` is SN.  The generalisation revealed that the body need NOT
be assumed strongly normalizing — the contractum's accessibility already bounds every body
reduction — so this corollary takes two hypotheses, not three. -/
theorem betaRedex_isStronglyNormalizing_of_contractum {scope : Nat}
    {body : RawTerm (scope + 1)} {argument : RawTerm scope}
    (argumentSN : IsStronglyNormalizing argument)
    (contractumSN : IsStronglyNormalizing (RawTerm.subst0 body argument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
          (.childCons argument .childNil))) :=
  betaSpineHeadExpansion (spine := []) argumentSN contractumSN

end StepStar
end FX1Poly.Core
