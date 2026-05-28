import LeanFX2.Foundation.PolyCell.Core.StrongNormalizationConstructors

/-! # Foundation/PolyCell/Core/StrongNormalizationNeutral
    - first neutral application accessibility endpoint

The constructor and redex SN files cover normal leaves, congruence-only
wrappers, and projection-shaped root redexes.  This file starts the neutral
application layer: applications whose head cannot reduce and cannot be a
lambda.  Such applications have no beta path, so their only outgoing steps are
argument congruence steps.

This is deliberately weaker than application closure.  General application SN
needs reducibility, because a normalizing function child may reduce to a lambda
and then fire beta.  The theorem here only covers stuck heads such as variables.
-/

namespace LeanFX2.Foundation.PolyCell.Core
namespace StepStar

/-- Application closure for heads that are neutral by an explicit invariant.

The invariant must prove two facts: neutral heads are not lambdas, and one-step
reduction from a neutral head stays neutral.  Under those hypotheses, beta is
impossible at every reduct of the head, so application accessibility follows
from nested accessibility induction over the head and argument. -/
theorem app_isStronglyNormalizing_of_neutral_head_arg
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {headTerm argumentTerm : RawTerm scope}
    (headIsNeutral : isNeutralHead headTerm)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ lambdaBody : RawTerm (scope + 1),
          currentHead ≠ .mkGen .gen_lam () (.childCons lambdaBody .childNil))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (headTerminates : IsStronglyNormalizing headTerm)
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons headTerm (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentHead =>
      isNeutralHead currentHead →
        ∀ {currentArgument : RawTerm scope},
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (.mkGen .gen_app ()
                (.childCons currentHead
                  (.childCons currentArgument .childNil)) : RawTerm scope))
    (m := fun currentHead _ headIH => by
      intro currentHeadIsNeutral currentArgument currentArgumentTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerArgument =>
            IsStronglyNormalizing
              (.mkGen .gen_app ()
                (.childCons currentHead
                  (.childCons innerArgument .childNil)) : RawTerm scope))
          (m := fun currentArgument currentArgumentSuccessors argumentIH =>
            Acc.intro
              (.mkGen .gen_app ()
                (.childCons currentHead
                  (.childCons currentArgument .childNil)) : RawTerm scope)
              (fun targetTerm applicationStep => by
                cases Step.from_app applicationStep with
                | inl betaBranch =>
                    obtain ⟨lambdaBody, headEq, _⟩ := betaBranch
                    exact False.elim
                      (neutralHeadIsNotLambda currentHeadIsNeutral
                        lambdaBody headEq)
                | inr congruenceBranch =>
                    cases congruenceBranch with
                    | inl headBranch =>
                        obtain ⟨targetHead, targetEq, headStep⟩ :=
                          headBranch
                        rw [targetEq]
                        exact headIH targetHead headStep
                          (neutralHeadStep currentHeadIsNeutral headStep)
                          (Acc.intro currentArgument
                            currentArgumentSuccessors)
                    | inr argumentBranch =>
                        obtain ⟨argumentAfter, targetEq, argumentStep⟩ :=
                          argumentBranch
                        rw [targetEq]
                        exact argumentIH argumentAfter argumentStep))
          currentArgumentTerminates)
    headTerminates)
    headIsNeutral
    argumentTerminates

/-- A neutral application with a normal non-lambda head is strongly
normalizing when its argument is strongly normalizing.

This is the safe application foothold: beta is ruled out by `headIsNotLambda`,
function congruence is ruled out by `headHasNoStep`, and the remaining steps are
exactly argument congruence steps. -/
theorem app_isStronglyNormalizing_of_normal_nonlambda_head_arg
    {scope : Nat} {headTerm argumentTerm : RawTerm scope}
    (headHasNoStep :
      ∀ targetHead : RawTerm scope, Step headTerm targetHead → False)
    (headIsNotLambda :
      ∀ lambdaBody : RawTerm (scope + 1),
        headTerm ≠ .mkGen .gen_lam () (.childCons lambdaBody .childNil))
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons headTerm (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentArgument =>
      IsStronglyNormalizing
        (.mkGen .gen_app ()
          (.childCons headTerm (.childCons currentArgument .childNil)) :
          RawTerm scope))
    (m := fun currentArgument _ argumentIH =>
      Acc.intro
        (.mkGen .gen_app ()
          (.childCons headTerm (.childCons currentArgument .childNil)) :
          RawTerm scope)
        (fun targetTerm applicationStep => by
          cases Step.from_app applicationStep with
          | inl betaBranch =>
              obtain ⟨lambdaBody, headEq, _⟩ := betaBranch
              exact False.elim (headIsNotLambda lambdaBody headEq)
          | inr congruenceBranch =>
              cases congruenceBranch with
              | inl headBranch =>
                  obtain ⟨targetHead, _, headStep⟩ := headBranch
                  exact False.elim (headHasNoStep targetHead headStep)
              | inr argumentBranch =>
                  obtain ⟨argumentAfter, targetEq, argumentStep⟩ :=
                    argumentBranch
                  rw [targetEq]
                  exact argumentIH argumentAfter argumentStep))
    argumentTerminates

/-- Variable-headed applications are strongly normalizing when their argument
is strongly normalizing.

This is the first concrete neutral application endpoint.  It does not claim
general application closure or beta closure. -/
theorem appVar_isStronglyNormalizing_of_argument {scope : Nat}
    (headIndex : Fin scope) {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_var headIndex .childNil)
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  app_isStronglyNormalizing_of_normal_nonlambda_head_arg
    (headTerm := .mkGen .gen_var headIndex .childNil)
    (argumentTerm := argumentTerm)
    (fun targetHead headStep =>
      noStep_var headIndex (targetTerm := targetHead) headStep)
    (fun lambdaBody headEq => by
      cases headEq)
    argumentTerminates

/-- A two-argument variable-headed application spine is strongly normalizing
when both arguments are strongly normalizing.

This is the first use of the neutral-head invariant closure: the head
`app (var i) firstArgument` may reduce through `firstArgument`, but every such
reduct is still an application with variable head, never a lambda. -/
theorem appVarSpine2_isStronglyNormalizing_of_arguments {scope : Nat}
    (headIndex : Fin scope)
    {firstArgument secondArgument : RawTerm scope}
    (firstTerminates : IsStronglyNormalizing firstArgument)
    (secondTerminates : IsStronglyNormalizing secondArgument) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_var headIndex .childNil)
              (.childCons firstArgument .childNil)))
          (.childCons secondArgument .childNil)) :
        RawTerm scope) :=
  app_isStronglyNormalizing_of_neutral_head_arg
    (isNeutralHead := fun candidateHead =>
      ∃ currentFirstArgument : RawTerm scope,
        candidateHead =
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_var headIndex .childNil)
              (.childCons currentFirstArgument .childNil)) :
            RawTerm scope))
    (headIsNeutral := ⟨firstArgument, rfl⟩)
    (neutralHeadIsNotLambda := fun candidateHeadIsNeutral lambdaBody
        candidateHeadEq => by
      obtain ⟨currentFirstArgument, candidateHeadShape⟩ :=
        candidateHeadIsNeutral
      rw [candidateHeadShape] at candidateHeadEq
      cases candidateHeadEq)
    (neutralHeadStep := fun candidateHeadIsNeutral candidateHeadStep => by
      obtain ⟨currentFirstArgument, candidateHeadShape⟩ :=
        candidateHeadIsNeutral
      rw [candidateHeadShape] at candidateHeadStep
      cases Step.from_app candidateHeadStep with
      | inl betaBranch =>
          obtain ⟨lambdaBody, variableEq, _⟩ := betaBranch
          cases variableEq
      | inr congruenceBranch =>
          cases congruenceBranch with
          | inl variableBranch =>
              obtain ⟨targetHead, _, variableStep⟩ := variableBranch
              exact False.elim
                (noStep_var headIndex (targetTerm := targetHead)
                  variableStep)
          | inr argumentBranch =>
              obtain ⟨argumentAfter, targetEq, _⟩ := argumentBranch
              exact ⟨argumentAfter, targetEq⟩)
    (headTerminates :=
      appVar_isStronglyNormalizing_of_argument headIndex firstTerminates)
    secondTerminates

end StepStar
end LeanFX2.Foundation.PolyCell.Core
