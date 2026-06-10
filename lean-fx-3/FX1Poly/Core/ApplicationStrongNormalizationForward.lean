import FX1Poly.Core.StepInversion
import FX1Poly.Core.StepSubst
import FX1Poly.Core.StrongNormalizationApplication

/-! # FX1Poly/Core/ApplicationStrongNormalizationForward
    — strong normalization of an application, CONSTRUCTED from SN of its parts plus a β-side-condition

`StrongNormalizationApplication` proves the DESCENT direction (SN of `app f a` gives SN of `f`).  This file
proves the FORWARD / CONSTRUCTIVE direction: `app f a` is strongly normalizing when

  * the function `f` is SN,
  * the argument `a` is SN, AND
  * every β-contraction is SN — for every `body` with `f ↝* lam body`, the contractum `body[a]` is SN.

The β-side-condition is ESSENTIAL and cannot be dropped: SN of the two positions alone does NOT give SN of
the application.  The classic counterexample is `Ω`: with `selfApp := lam (app v0 v0)` (which is SN — it is a
`lam` whose body is neutral), the application `app selfApp selfApp` β-reduces to `app selfApp selfApp` again
and loops forever.  What fails the hypotheses is precisely the β-side-condition: `selfApp ↝* lam (app v0 v0)`
(reflexively) yet the contractum `(app v0 v0)[selfApp] = app selfApp selfApp` is NOT SN.  So the side-condition
is exactly the content the Ω term lacks — the honest statement of "application preserves SN".

This is the load-bearing lemma for MEMBER WEAK-HEAD-EXPANSION of the stratified reducibility candidate: the Π
arm of `headExpand` (the deferred conditional hypothesis carried by every recursor-value reducibility lemma —
`natElimValueReducibility`, `listElimValueReducibility`, …) needs exactly "an application of a reducible
function to a reducible argument is SN", and a reducible function applied to a reducible argument satisfies the
β-side-condition by the function candidate's own arrow membership.

## Proof shape

Nested accessibility induction.  The auxiliary carries `∀ argument` (plus the SN-argument and β-side-condition
premises) IN ITS CONCLUSION, so `induction functionStronglyNormalizing` naturally generalizes the argument;
the inner `induction argumentStronglyNormalizing` then gives both well-founded induction hypotheses.  At a step
of `app f a`, `Step.from_app` splits three ways:

  * β-contraction (`f = lam body`, reduct `= body[a]`) — discharged by the β-side-condition at the reflexive
    chain;
  * function congruence (`f ↝ f'`) — the function IH, transporting the β-side-condition along
    `StepStar.trans functionStep`;
  * argument congruence (`a ↝ a'`) — the argument IH, transporting each contractum's SN forward along
    `Step.subst0Argument` via `IsStronglyNormalizing.descendStepStar`.

## Zero-axiom verification

`Acc.rec` nested induction + `Step.from_app` 3-way inversion + `Step.subst0Argument` + the forward-closure
`IsStronglyNormalizing.descendStepStar` (iterated `Acc.inv`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega` (verified by `#print axioms` in scratch before landing).  Gated per
declaration in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **Forward strong-normalization closure along a reduction chain.**  If `sourceTerm` is strongly
normalizing and `sourceTerm ↝* reductTerm`, then `reductTerm` is strongly normalizing.  This is the
`StepStar`-iterated form of the single-step forward closure `Acc.inv` (every reduct of an SN term is SN). -/
theorem IsStronglyNormalizing.descendStepStar {scope : Nat} {sourceTerm reductTerm : RawTerm scope}
    (sourceStronglyNormalizing : IsStronglyNormalizing sourceTerm)
    (chain : StepStar sourceTerm reductTerm) :
    IsStronglyNormalizing reductTerm := by
  induction chain with
  | refl => exact sourceStronglyNormalizing
  | trans headStep _rest restIH => exact restIH (sourceStronglyNormalizing.inv headStep)

/-- **Auxiliary (argument generalized in the conclusion).**  Inducting on the function's SN witness here
generalizes the argument so the function IH applies at every function reduct.  See the file docstring for the
3-way `Step.from_app` split. -/
theorem isStronglyNormalizing_applicationCell_aux {scope : Nat} {functionTerm : RawTerm scope}
    (functionStronglyNormalizing : IsStronglyNormalizing functionTerm) :
    ∀ argument : RawTerm scope, IsStronglyNormalizing argument →
      (∀ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)),
        StepStar functionTerm
          (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) →
        IsStronglyNormalizing (RawTerm.subst0 body argument)) →
      IsStronglyNormalizing (applicationCell functionTerm argument) := by
  induction functionStronglyNormalizing with
  | intro functionWitness _functionAccessors functionIH =>
      intro argument argumentStronglyNormalizing
      induction argumentStronglyNormalizing with
      | intro argumentWitness _argumentAccessors argumentIH =>
          intro betaContractionsStronglyNormalizing
          apply Acc.intro
          intro reduct stepToReduct
          rcases Step.from_app stepToReduct with
            ⟨domainAnn, body, functionIsLam, reductIsContractum⟩ |
            ⟨functionAfter, reductIsFunctionStep, functionStep⟩ |
            ⟨argumentAfter, reductIsArgumentStep, argumentStep⟩
          · subst reductIsContractum
            subst functionIsLam
            exact betaContractionsStronglyNormalizing domainAnn body (StepStar.refl _)
          · subst reductIsFunctionStep
            exact functionIH functionAfter functionStep argumentWitness
              (Acc.intro argumentWitness _argumentAccessors)
              (fun domainAnn body chain =>
                betaContractionsStronglyNormalizing domainAnn body
                  (StepStar.trans functionStep chain))
          · subst reductIsArgumentStep
            refine argumentIH argumentAfter argumentStep (fun domainAnn body chain => ?_)
            exact IsStronglyNormalizing.descendStepStar
              (betaContractionsStronglyNormalizing domainAnn body chain)
              (Step.subst0Argument body argumentStep)

/-- **SN of an application under the β-contraction side-condition.**  `app functionTerm argument` is strongly
normalizing when the function and argument are SN AND every β-contraction of the function (once it
weak-head-reduces to a `lam`) against the argument is SN.  The side-condition is essential — SN of the two
positions alone does NOT give SN of the application (the Ω term, see the file docstring).  This is the honest
form of "application preserves strong normalization" and the load-bearing ingredient for member
weak-head-expansion (the Π arm of the recursor-value `headExpand` hypothesis). -/
theorem isStronglyNormalizing_applicationCell_ofBetaContractionsStronglyNormalizing
    {scope : Nat} {functionTerm argument : RawTerm scope}
    (functionStronglyNormalizing : IsStronglyNormalizing functionTerm)
    (argumentStronglyNormalizing : IsStronglyNormalizing argument)
    (betaContractionsStronglyNormalizing :
        ∀ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)),
        StepStar functionTerm
          (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) →
        IsStronglyNormalizing (RawTerm.subst0 body argument)) :
    IsStronglyNormalizing (applicationCell functionTerm argument) :=
  isStronglyNormalizing_applicationCell_aux functionStronglyNormalizing argument
    argumentStronglyNormalizing betaContractionsStronglyNormalizing

end FX1Poly.Core
