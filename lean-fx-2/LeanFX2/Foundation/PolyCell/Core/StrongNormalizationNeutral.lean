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

end StepStar
end LeanFX2.Foundation.PolyCell.Core
