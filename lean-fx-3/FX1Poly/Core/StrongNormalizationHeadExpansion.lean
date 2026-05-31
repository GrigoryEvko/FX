import FX1Poly.Core.ReducibilityCandidate
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

end StepStar
end FX1Poly.Core
