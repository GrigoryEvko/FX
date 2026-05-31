import FX1Poly.Core.HeadStep
import FX1Poly.Core.StepInversion
import FX1Poly.Core.StepSubst
import FX1Poly.Core.StepStar

/-! # Foundation/PolyCell/Core/HeadStepCommute2
    — weak-head reduction commutes with arbitrary single-step reduction

The conversion-invariance of the dependent reducibility relation (`ReducibleType`) turns, in its
`headExpand` arm, on a single structural fact: how a deterministic weak-head step (`HeadStep`) and an
ARBITRARY single step (`Step`) out of the *same* term relate.  They form a local commutation diamond:

```
        HeadStep            Step
  term ──────────► reduct ,  term ──────────► other
```

Either the arbitrary step landed on the very head redex the weak-head step contracts (`other = reduct`),
or the head redex SURVIVES the arbitrary step — `other` still weak-head steps, and the two contracta
re-converge (`reduct ↠ otherReduct ↞ᴴ other`).  Crucially the convergence on the `reduct` side is a
`StepStar` chain, NOT a single step: an argument reduction `arg ↝ arg'` under a head β-redex
`(λb) arg` is replicated once per occurrence of variable 0 in `b` when the redex fires, so
`subst0 b arg ↠ subst0 b arg'` is a multi-step replay (`Step.subst0Argument`).

This is exactly the engine the head-expansion case of conversion-invariance consumes: given a step out
of a `headExpand`-typed code, this lemma either identifies it with the stored contractum or relocates
the head reduction past it, keeping the candidate fixed.  No confluence (`cd_lemma`) is needed — only
the determinism-friendly head/arbitrary commutation, the lambda-body and argument substitution replays
(`Step.subst0Body` / `Step.subst0Argument`), and the application-congruence `StepStar` lifts
(`StepStar.appFunction` / `StepStar.appArgument`).

## Zero-axiom verification

Induction on the `HeadStep` derivation; the arbitrary step is inverted by the audit-clean
`Step.from_app` / `Step.from_lam` (and, in the head β-case, raw `cases`, whose β/β overlap unifies the
two contracta to `rfl`, sidestepping `mkGen` injectivity).  Impossible spine positions close by
`StepChildren.no_step_at_empty_spine`; the β-into-`appCongruence` impossibility by `HeadStep.not_from_lam`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Weak-head reduction commutes with arbitrary single-step reduction.**  Given a weak-head step
`term ↝ᴴ reduct` and any step `term ↝ other`, either the arbitrary step contracted the same head redex
(`other = reduct`), or the head redex survives — `other` weak-head steps to some `otherReduct` and the
stored contractum catches up by a `StepStar` chain (`reduct ↠ otherReduct`). -/
theorem HeadStep.commuteWithStep {scope : Nat} {term reduct : RawTerm scope}
    (headStep : HeadStep term reduct) :
    ∀ {other : RawTerm scope}, Step term other →
      other = reduct ∨
        ∃ otherReduct : RawTerm scope, HeadStep other otherReduct ∧ StepStar reduct otherReduct := by
  induction headStep with
  | @beta body argument =>
      intro other step
      cases step with
      | beta => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest functionStep =>
              obtain ⟨bodyAfter, functionEquation, bodyStep⟩ := Step.from_lam functionStep
              subst functionEquation
              exact Or.inr ⟨_, HeadStep.beta, Step.subst0Body argument bodyStep⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest argumentStep =>
                  exact Or.inr ⟨_, HeadStep.beta, Step.subst0Argument body argumentStep⟩
              | there _head emptyStep =>
                  exact absurd emptyStep StepChildren.no_step_at_empty_spine
  | @appCongruence function functionReduct argument functionHeadStep functionInductiveHypothesis =>
      intro other step
      rcases Step.from_app step with
        ⟨betaBody, functionEquation, _targetEquation⟩
        | ⟨functionAfter, targetEquation, functionStep⟩
        | ⟨argumentAfter, targetEquation, argumentStep⟩
      · rw [functionEquation] at functionHeadStep
        exact absurd functionHeadStep HeadStep.not_from_lam
      · subst targetEquation
        rcases functionInductiveHypothesis functionStep with
          functionAfterEquation | ⟨functionReduct2, headStep2, starChain⟩
        · subst functionAfterEquation
          exact Or.inl rfl
        · exact Or.inr
            ⟨.mkGen .gen_app () (.childCons functionReduct2 (.childCons argument .childNil)),
              HeadStep.appCongruence headStep2, StepStar.appFunction starChain⟩
      · subst targetEquation
        exact Or.inr
          ⟨.mkGen .gen_app () (.childCons functionReduct (.childCons argumentAfter .childNil)),
            HeadStep.appCongruence functionHeadStep,
            StepStar.appArgument functionReduct (StepStar.single argumentStep)⟩

end FX1Poly.Core
