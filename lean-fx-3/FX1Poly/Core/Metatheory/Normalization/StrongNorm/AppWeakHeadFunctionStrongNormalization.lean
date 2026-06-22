import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSpineExpansion
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepCommute

/-! # FX1Poly/Core/AppWeakHeadFunctionStrongNormalization
    — strong normalization of an application whose FUNCTION is weak-head-reducible (the arrow member-WHE spine)

`betaSpineHeadExpansion` proved an application spine over a β-redex `app (lam body) arg` is strongly
normalizing from the contractum's SN.  The general member weak-head expansion needs the SAME fact for an
application whose function is reducible by ANY weak-head step — not just β, but root-ι and the ten
scrutinee-congruence rules (so the function may be an eliminator cell whose scrutinee is still reducing).

`appWeakHeadFunction_isStronglyNormalizing`: if `source ↝ʰ reduct` (any weak-head step), `source` is SN,
`argument` is SN, and `app reduct argument` is SN, then `app source argument` is SN.

The argument cannot be `SN source ∧ SN argument ⟹ SN (app source argument)` (FALSE in general — `Ω`).  The
extra datum is `SN (app reduct argument)`: the application's weak-head reduct is already SN, and `source`'s
weak-head redex IS the application's, so every reduct of `app source argument` is dominated.  The proof is the
nested `Acc` induction of `betaSpineHeadExpansion`, but where the reduct is THREADED and updated by the
commutation diamond:

  * **β** (`source = lam …`) is IMPOSSIBLE — a λ has no weak-head step (`WeakHeadStep.not_from_lam` refutes the
    threaded `source ↝ʰ reduct`).  This is the cleaner analogue of `betaSpineHeadExpansion`'s β arm (there the
    redex itself; here the redex is excluded by construction).
  * **function congruence** `source ↝ source'`: by `WeakHeadStep.commuteWithStep`, either `source' = reduct`
    (the application reduct is SN by hypothesis) or `source' ↝ʰ reduct'` with `reduct ↠ reduct'`; the
    application reduct catches up (`StepStar.appFunction`), and the source `Acc` induction recurses on the
    smaller `source'` with the updated `reduct'`.
  * **argument congruence** `argument ↝ argument'`: the application reduct catches up
    (`StepStar.appArgument`), and the argument `Acc` induction recurses on the smaller `argument'`.

This is the genuinely-new Tait spine fact behind the bounded arrow member weak-head expansion (the `piArm` of
`memberWeakHeadExpansionModuloPi`) — and hence behind the native data-eliminator fundamental-theorem rows.

## Zero-axiom verification

`Step.from_app` inversion + `WeakHeadStep.commuteWithStep` + `WeakHeadStep.not_from_lam` +
`isStronglyNormalizing_of_stepStar` + `StepStar.appFunction`/`appArgument`, under a nested `Acc.rec`.  No
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Tier0.Syntax
open StepStar

/-- **An application is strongly normalizing when its function is weak-head-reducible to an SN-applied
reduct.**  Given a weak-head step `source ↝ʰ reduct`, `source`/`argument` both SN, and the weak-head reduct
application `app reduct argument` SN, the application `app source argument` is SN.  The arrow analogue of
`betaSpineHeadExpansion` with the reduct threaded through the commutation diamond — the SN spine behind the
arrow candidate's member weak-head expansion. -/
theorem appWeakHeadFunction_isStronglyNormalizing {scope : Nat}
    {source reduct argument : RawTerm scope}
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (weakHeadStep : WeakHeadStep source reduct)
    (argumentStronglyNormalizing : IsStronglyNormalizing argument)
    (reductApplicationStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_app () (.childCons reduct (.childCons argument .childNil)))) :
    IsStronglyNormalizing
      (.mkGen .gen_app () (.childCons source (.childCons argument .childNil))) := by
  suffices general :
      ∀ {currentSource : RawTerm scope}, Acc StepSuccessor currentSource →
        ∀ {currentArgument : RawTerm scope}, Acc StepSuccessor currentArgument →
          ∀ {currentReduct : RawTerm scope}, WeakHeadStep currentSource currentReduct →
            IsStronglyNormalizing
              (.mkGen .gen_app ()
                (.childCons currentReduct (.childCons currentArgument .childNil))) →
            IsStronglyNormalizing
              (.mkGen .gen_app ()
                (.childCons currentSource (.childCons currentArgument .childNil))) from
    general sourceStronglyNormalizing argumentStronglyNormalizing weakHeadStep
      reductApplicationStronglyNormalizing
  intro currentSource sourceAccessible
  induction sourceAccessible with
  | intro sourceFocus _sourcePredecessorsAccessible sourceInductiveHypothesis =>
    intro currentArgument argumentAccessible
    induction argumentAccessible with
    | intro argumentFocus argumentPredecessorsAccessible argumentInductiveHypothesis =>
        intro currentReduct weakHeadStepFromFocus reductApplicationSN
        apply Acc.intro
        intro applicationReduct applicationStep
        rcases Step.from_app applicationStep with
          ⟨_domainAnn, _body, functionIsLam, _targetEq⟩ |
          ⟨functionAfter, targetEq, functionStep⟩ |
          ⟨argumentAfter, targetEq, argumentStep⟩
        · -- β: the function would be a λ, but a λ has no weak-head step.
          rw [functionIsLam] at weakHeadStepFromFocus
          exact absurd weakHeadStepFromFocus WeakHeadStep.not_from_lam
        · -- function congruence: `sourceFocus ↝ functionAfter`.
          subst targetEq
          rcases WeakHeadStep.commuteWithStep weakHeadStepFromFocus functionAfter functionStep with
            reductEquation | ⟨updatedReduct, functionAfterWeakHeadStep, reductChain⟩
          · -- the step contracted the very weak-head redex: the application reduct is SN by hypothesis.
            rw [reductEquation]; exact reductApplicationSN
          · -- the redex survived: catch the application reduct up, recurse on the smaller function.
            have updatedReductApplicationSN :
                IsStronglyNormalizing
                  (.mkGen .gen_app ()
                    (.childCons updatedReduct (.childCons argumentFocus .childNil))) :=
              isStronglyNormalizing_of_stepStar (StepStar.appFunction reductChain) reductApplicationSN
            exact sourceInductiveHypothesis functionAfter functionStep
              (Acc.intro argumentFocus argumentPredecessorsAccessible)
              functionAfterWeakHeadStep updatedReductApplicationSN
        · -- argument congruence: `argumentFocus ↝ argumentAfter`.
          subst targetEq
          have reductArgumentAfterSN :
              IsStronglyNormalizing
                (.mkGen .gen_app ()
                  (.childCons currentReduct (.childCons argumentAfter .childNil))) :=
            isStronglyNormalizing_of_stepStar
              (StepStar.appArgument currentReduct (StepStar.single argumentStep)) reductApplicationSN
          exact argumentInductiveHypothesis argumentAfter argumentStep weakHeadStepFromFocus
            reductArgumentAfterSN

end FX1Poly.Core
