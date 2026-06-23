import FX1Poly.Core.Rewriting.Reduction.Step.StepInversion
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.ApplicationStrongNormalizationForward

/-! # FX1Poly/Core/PathApplicationStrongNormalizationForward
    — strong normalization of a path application, CONSTRUCTED from SN of its parts plus an endpoint-β side-condition

The path-application twin of `ApplicationStrongNormalizationForward`: `pathApp path argument` is strongly
normalizing when

  * the path `path` is SN,
  * the interval endpoint `argument` is SN, AND
  * every endpoint-β contraction is SN — for every `body` with `path ↝* pathLam body`, the contractum
    `body[argument]` is SN.

The endpoint-β rule `pathApp (pathLam body) arg ↝ body[arg]` is a GENUINE β-redex (a substitution into the
body), NOT a structural data eliminator that contracts to a passive branch — so the β-side-condition is
ESSENTIAL and cannot be dropped.  The Ω obstruction transfers verbatim from the `app` case (SN of the two
positions alone does NOT give SN of the application).  This is the honest "path application preserves strong
normalization", and the load-bearing SN ingredient for the `pathApp` member weak-head-expansion: the value
handler of the bridge eliminator member, once the path reaches `pathLam body`, gets the contractum's SN from its
reducibility-member residue — exactly this side-condition.

`gen_pathLam` carries NO domain annotation (one child, the body under one binder), so the side-condition
quantifies over `body` alone — the single structural difference from the `gen_app` / `gen_lam` original (whose
`lam` carries a domain annotation).

## Zero-axiom verification

Nested `Acc.rec` induction + `Step.from_pathApp` 3-way inversion + `Step.subst0Argument` + the forward-closure
`IsStronglyNormalizing.descendStepStar` — the verbatim shape of `isStronglyNormalizing_applicationCell_aux`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **Auxiliary (argument generalized in the conclusion).**  The path-application twin of
`isStronglyNormalizing_applicationCell_aux`: inducting on the path's SN witness generalizes the argument so the
path IH applies at every path reduct.  `Step.from_pathApp` splits three ways — endpoint-β (the side-condition at
the reflexive chain), path congruence (the path IH, transporting the side-condition along `StepStar.trans`),
argument congruence (the argument IH, transporting each contractum's SN forward along `Step.subst0Argument`). -/
theorem isStronglyNormalizing_pathApplicationCell_aux {scope : Nat} {pathTerm : RawTerm scope}
    (pathStronglyNormalizing : IsStronglyNormalizing pathTerm) :
    ∀ argument : RawTerm scope, IsStronglyNormalizing argument →
      (∀ body : RawTerm (scope + 1),
        StepStar pathTerm (.mkGen .gen_pathLam () (.childCons body .childNil)) →
        IsStronglyNormalizing (RawTerm.subst0 body argument)) →
      IsStronglyNormalizing
        (.mkGen .gen_pathApp () (.childCons pathTerm (.childCons argument .childNil))) := by
  induction pathStronglyNormalizing with
  | intro pathWitness _pathAccessors pathIH =>
      intro argument argumentStronglyNormalizing
      induction argumentStronglyNormalizing with
      | intro argumentWitness _argumentAccessors argumentIH =>
          intro endpointBetaContractionsStronglyNormalizing
          apply Acc.intro
          intro reduct stepToReduct
          rcases Step.from_pathApp stepToReduct with
            ⟨body, pathIsPathLam, reductIsContractum⟩ |
            ⟨pathAfter, reductIsPathStep, pathStep⟩ |
            ⟨argumentAfter, reductIsArgumentStep, argumentStep⟩
          · subst reductIsContractum
            subst pathIsPathLam
            exact endpointBetaContractionsStronglyNormalizing body (StepStar.refl _)
          · subst reductIsPathStep
            exact pathIH pathAfter pathStep argumentWitness
              (Acc.intro argumentWitness _argumentAccessors)
              (fun body chain =>
                endpointBetaContractionsStronglyNormalizing body
                  (StepStar.trans pathStep chain))
          · subst reductIsArgumentStep
            refine argumentIH argumentAfter argumentStep (fun body chain => ?_)
            exact IsStronglyNormalizing.descendStepStar
              (endpointBetaContractionsStronglyNormalizing body chain)
              (Step.subst0Argument body argumentStep)

/-- **SN of a path application under the endpoint-β side-condition.**  `pathApp pathTerm argument` is strongly
normalizing when the path and the interval endpoint are SN AND every endpoint-β contraction of the path (once it
weak-head-reduces to a `pathLam`) against the argument is SN.  The side-condition is essential — SN of the two
positions alone does NOT give SN of the path application (the Ω obstruction, see the file docstring).  This is
the honest form of "path application preserves strong normalization" and the load-bearing ingredient for the
`pathApp` member weak-head-expansion (the value handler's contractum SN comes from its reducibility residue). -/
theorem isStronglyNormalizing_pathApplicationCell_ofEndpointBetaContractionsStronglyNormalizing
    {scope : Nat} {pathTerm argument : RawTerm scope}
    (pathStronglyNormalizing : IsStronglyNormalizing pathTerm)
    (argumentStronglyNormalizing : IsStronglyNormalizing argument)
    (endpointBetaContractionsStronglyNormalizing :
        ∀ body : RawTerm (scope + 1),
        StepStar pathTerm (.mkGen .gen_pathLam () (.childCons body .childNil)) →
        IsStronglyNormalizing (RawTerm.subst0 body argument)) :
    IsStronglyNormalizing
      (.mkGen .gen_pathApp () (.childCons pathTerm (.childCons argument .childNil))) :=
  isStronglyNormalizing_pathApplicationCell_aux pathStronglyNormalizing argument
    argumentStronglyNormalizing endpointBetaContractionsStronglyNormalizing

end FX1Poly.Core
