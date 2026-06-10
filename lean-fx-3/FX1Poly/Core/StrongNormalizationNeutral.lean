import FX1Poly.Core.StrongNormalizationConstructors

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

namespace FX1Poly.Core
namespace StepStar

/-- The one-step extension of a neutral-head predicate through application.

`IsNeutralApplicationHead isNeutralHead candidateHead` says that
`candidateHead` is an application whose function child is neutral.  This
predicate is the reusable spine step: it lets neutral application spines grow
without re-proving the beta-exclusion and congruence closure argument for each
concrete arity. -/
def IsNeutralApplicationHead {scope : Nat}
    (isNeutralHead : RawTerm scope → Prop)
    (candidateHead : RawTerm scope) : Prop :=
  ∃ innerHead : RawTerm scope,
    ∃ innerArgument : RawTerm scope,
      isNeutralHead innerHead ∧
        candidateHead =
          (.mkGen .gen_app ()
            (.childCons innerHead (.childCons innerArgument .childNil)) :
            RawTerm scope)

/-- Extending a neutral predicate through application still cannot produce a
lambda head. -/
theorem isNeutralApplicationHead_not_lam {scope : Nat}
    {isNeutralHead : RawTerm scope → Prop}
    {candidateHead : RawTerm scope}
    (candidateHeadIsNeutralApplication :
      IsNeutralApplicationHead isNeutralHead candidateHead)
    (lambdaDomain : RawTerm scope)
    (lambdaBody : RawTerm (scope + 1)) :
    candidateHead ≠
      (.mkGen .gen_lam ()
        (.childCons lambdaDomain (.childCons lambdaBody .childNil)) :
      RawTerm scope) := by
  obtain
    ⟨innerHead, innerArgument, innerHeadIsNeutral, candidateHeadShape⟩ :=
      candidateHeadIsNeutralApplication
  rw [candidateHeadShape]
  intro applicationEq
  cases applicationEq

/-- Extending a neutral predicate through application is closed under one
source step when the original neutral predicate is closed under one source
step.  Beta remains impossible because the inner head is neutral. -/
theorem isNeutralApplicationHead_step {scope : Nat}
    {isNeutralHead : RawTerm scope → Prop}
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    {candidateHead targetHead : RawTerm scope}
    (candidateHeadIsNeutralApplication :
      IsNeutralApplicationHead isNeutralHead candidateHead)
    (candidateHeadStep : Step candidateHead targetHead) :
    IsNeutralApplicationHead isNeutralHead targetHead := by
  obtain
    ⟨innerHead, innerArgument, innerHeadIsNeutral, candidateHeadShape⟩ :=
      candidateHeadIsNeutralApplication
  rw [candidateHeadShape] at candidateHeadStep
  cases Step.from_app candidateHeadStep with
  | inl betaBranch =>
      obtain ⟨lambdaDomain, lambdaBody, innerHeadEq, _⟩ := betaBranch
      exact False.elim
        (neutralHeadIsNotLambda innerHeadIsNeutral lambdaDomain lambdaBody
          innerHeadEq)
  | inr congruenceBranch =>
      cases congruenceBranch with
      | inl headBranch =>
          obtain ⟨innerHeadAfter, targetEq, innerHeadStep⟩ := headBranch
          exact
            ⟨ innerHeadAfter
            , innerArgument
            , neutralHeadStep innerHeadIsNeutral innerHeadStep
            , targetEq ⟩
      | inr argumentBranch =>
          obtain ⟨innerArgumentAfter, targetEq, _⟩ := argumentBranch
          exact ⟨innerHead, innerArgumentAfter, innerHeadIsNeutral, targetEq⟩

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
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
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
                    obtain ⟨lambdaDomain, lambdaBody, headEq, _⟩ := betaBranch
                    exact False.elim
                      (neutralHeadIsNotLambda currentHeadIsNeutral
                        lambdaDomain lambdaBody headEq)
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

/-- Application closure for one more neutral-spine argument.

This packages the reusable spine-extension predicate with the generic neutral
application theorem: a neutral application head remains stuck under beta, so
adding a strongly-normalizing argument preserves accessibility. -/
theorem app_isStronglyNormalizing_of_neutral_application_head_arg
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {headTerm argumentTerm : RawTerm scope}
    (headIsNeutralApplication :
      IsNeutralApplicationHead isNeutralHead headTerm)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
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
  app_isStronglyNormalizing_of_neutral_head_arg
    (isNeutralHead := IsNeutralApplicationHead isNeutralHead)
    headIsNeutralApplication
    (fun currentHeadIsNeutralApplication lambdaDomain lambdaBody =>
      isNeutralApplicationHead_not_lam currentHeadIsNeutralApplication
        lambdaDomain lambdaBody)
    (fun currentHeadIsNeutralApplication currentHeadStep =>
      isNeutralApplicationHead_step neutralHeadIsNotLambda neutralHeadStep
        currentHeadIsNeutralApplication currentHeadStep)
    headTerminates
    argumentTerminates

/-- Neutral predicate for any application spine rooted at a variable. -/
inductive IsVariableHeadedSpine {scope : Nat} (headIndex : Fin scope) :
    RawTerm scope → Prop
  | rootVariable :
      IsVariableHeadedSpine headIndex
        (.mkGen .gen_var headIndex .childNil)
  | applyArgument {headTerm argumentTerm : RawTerm scope} :
      IsVariableHeadedSpine headIndex headTerm →
        IsVariableHeadedSpine headIndex
          (.mkGen .gen_app ()
            (.childCons headTerm (.childCons argumentTerm .childNil)))

/-- A variable-headed application spine is syntactically never a lambda. -/
theorem isVariableHeadedSpine_not_lam {scope : Nat}
    {headIndex : Fin scope} {candidateHead : RawTerm scope}
    (candidateHeadIsVariableSpine :
      IsVariableHeadedSpine headIndex candidateHead)
    (lambdaDomain : RawTerm scope)
    (lambdaBody : RawTerm (scope + 1)) :
    candidateHead ≠
      (.mkGen .gen_lam ()
        (.childCons lambdaDomain (.childCons lambdaBody .childNil)) :
      RawTerm scope) := by
  intro candidateEq
  cases candidateHeadIsVariableSpine with
  | rootVariable =>
      cases candidateEq
  | applyArgument _ =>
      cases candidateEq

/-- Variable-headed application spines are closed under one source step.

The root variable has no outgoing step.  For an application spine, beta is
impossible because the inner head is also a variable-headed spine; congruence
steps either preserve the spine root or step one argument. -/
theorem isVariableHeadedSpine_step {scope : Nat}
    {headIndex : Fin scope} {candidateHead targetHead : RawTerm scope}
    (candidateHeadIsVariableSpine :
      IsVariableHeadedSpine headIndex candidateHead)
    (candidateHeadStep : Step candidateHead targetHead) :
    IsVariableHeadedSpine headIndex targetHead := by
  induction candidateHeadIsVariableSpine generalizing targetHead with
  | rootVariable =>
      exact False.elim
        (noStep_var headIndex (targetTerm := targetHead)
          candidateHeadStep)
  | applyArgument innerHeadIsVariableSpine innerIH =>
      cases Step.from_app candidateHeadStep with
      | inl betaBranch =>
          obtain ⟨lambdaDomain, lambdaBody, innerHeadEq, _⟩ := betaBranch
          exact False.elim
            (isVariableHeadedSpine_not_lam innerHeadIsVariableSpine
              lambdaDomain lambdaBody innerHeadEq)
      | inr congruenceBranch =>
          cases congruenceBranch with
          | inl headBranch =>
              obtain ⟨innerHeadAfter, targetEq, innerHeadStep⟩ :=
                headBranch
              rw [targetEq]
              exact IsVariableHeadedSpine.applyArgument
                (innerIH innerHeadStep)
          | inr argumentBranch =>
              obtain ⟨argumentAfter, targetEq, _⟩ := argumentBranch
              rw [targetEq]
              exact IsVariableHeadedSpine.applyArgument
                innerHeadIsVariableSpine

/-- Adding a strongly-normalizing argument to any strongly-normalizing
variable-headed spine preserves strong normalization. -/
theorem app_isStronglyNormalizing_of_variable_headed_spine_arg
    {scope : Nat} {headIndex : Fin scope}
    {headTerm argumentTerm : RawTerm scope}
    (headIsVariableSpine : IsVariableHeadedSpine headIndex headTerm)
    (headTerminates : IsStronglyNormalizing headTerm)
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons headTerm (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  app_isStronglyNormalizing_of_neutral_head_arg
    (isNeutralHead := IsVariableHeadedSpine headIndex)
    headIsVariableSpine
    (fun variableSpineHead lambdaDomain lambdaBody =>
      isVariableHeadedSpine_not_lam variableSpineHead lambdaDomain lambdaBody)
    (fun variableSpineHead variableSpineStep =>
      isVariableHeadedSpine_step variableSpineHead variableSpineStep)
    headTerminates
    argumentTerminates

/-- Raw application helper used to state finite neutral-spine folds without
repeating the structural `gen_app` constructor shape. -/
def applyRawArgument {scope : Nat}
    (headTerm argumentTerm : RawTerm scope) : RawTerm scope :=
  (.mkGen .gen_app ()
    (.childCons headTerm (.childCons argumentTerm .childNil)) :
    RawTerm scope)

/-- Fold a list of arguments onto an existing raw head, left-to-right. -/
def applyRawArgumentsFrom {scope : Nat}
    (headTerm : RawTerm scope) : List (RawTerm scope) → RawTerm scope
  | [] => headTerm
  | argumentTerm :: remainingArguments =>
      applyRawArgumentsFrom
        (applyRawArgument headTerm argumentTerm)
        remainingArguments

/-- Variable-headed spine fold, kept as the variable-specific public name used
by existing finite-spine endpoints. -/
def variableHeadedSpineTermFrom {scope : Nat}
    (headTerm : RawTerm scope) (argumentTerms : List (RawTerm scope)) :
    RawTerm scope :=
  applyRawArgumentsFrom headTerm argumentTerms

/-- Fold a list of arguments onto a variable head, left-to-right. -/
def variableHeadedSpineTerm {scope : Nat}
    (headIndex : Fin scope) (argumentTerms : List (RawTerm scope)) :
    RawTerm scope :=
  variableHeadedSpineTermFrom
    (.mkGen .gen_var headIndex .childNil : RawTerm scope)
    argumentTerms

/-- Every argument in a finite raw-term list is strongly normalizing. -/
inductive AllStronglyNormalizingArguments {scope : Nat} :
    List (RawTerm scope) → Prop
  | nil : AllStronglyNormalizingArguments []
  | cons {argumentTerm : RawTerm scope}
      {remainingArguments : List (RawTerm scope)} :
      IsStronglyNormalizing argumentTerm →
      AllStronglyNormalizingArguments remainingArguments →
        AllStronglyNormalizingArguments
          (argumentTerm :: remainingArguments)

/-- Any finite application spine with a neutral head is strongly normalizing
when the head is strongly normalizing, every argument is strongly normalizing,
and the neutral invariant is closed under one source step.

This is the application-SN foothold needed before the Tait reducibility layer:
beta is ruled out at each spine head by the neutral invariant, while child
congruence is discharged by nested accessibility over the current head and the
next argument. -/
theorem applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_arguments
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {headTerm : RawTerm scope} {argumentTerms : List (RawTerm scope)}
    (headIsNeutral : isNeutralHead headTerm)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (headTerminates : IsStronglyNormalizing headTerm)
    (argumentTermsTerminate :
      AllStronglyNormalizingArguments argumentTerms) :
    IsStronglyNormalizing
      (applyRawArgumentsFrom headTerm argumentTerms) := by
  induction argumentTerms generalizing isNeutralHead headTerm with
  | nil =>
      exact headTerminates
  | cons argumentTerm remainingArguments inductionHypothesis =>
      cases argumentTermsTerminate with
      | cons argumentTerminates remainingArgumentsTerminate =>
          exact
            inductionHypothesis
              (isNeutralHead := IsNeutralApplicationHead isNeutralHead)
              (headTerm := applyRawArgument headTerm argumentTerm)
              ⟨headTerm, argumentTerm, headIsNeutral, rfl⟩
              (fun neutralApplicationHead lambdaDomain lambdaBody =>
                isNeutralApplicationHead_not_lam neutralApplicationHead
                  lambdaDomain lambdaBody)
              (fun neutralApplicationHead neutralApplicationStep =>
                isNeutralApplicationHead_step neutralHeadIsNotLambda
                  neutralHeadStep neutralApplicationHead neutralApplicationStep)
              (app_isStronglyNormalizing_of_neutral_head_arg
                isNeutralHead headIsNeutral neutralHeadIsNotLambda
                neutralHeadStep headTerminates argumentTerminates)
              remainingArgumentsTerminate

/-- One-argument specialization of the finite neutral-spine accessibility
helper.  This packages the common selected-branch iota reduct
`app neutralHead argument` without repeating the argument-list witness. -/
theorem applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_one_argument
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {headTerm argumentTerm : RawTerm scope}
    (headIsNeutral : isNeutralHead headTerm)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (headTerminates : IsStronglyNormalizing headTerm)
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (applyRawArgumentsFrom headTerm [argumentTerm]) :=
  applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_arguments
    (isNeutralHead := isNeutralHead)
    headIsNeutral
    neutralHeadIsNotLambda
    neutralHeadStep
    headTerminates
    (AllStronglyNormalizingArguments.cons argumentTerminates
      AllStronglyNormalizingArguments.nil)

/-- Two-argument specialization of the finite neutral-spine accessibility
helper.  This is the selected-branch shape used by successor eliminators:
`app (app neutralHead firstArgument) secondArgument`. -/
theorem applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_two_arguments
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {headTerm firstArgumentTerm secondArgumentTerm : RawTerm scope}
    (headIsNeutral : isNeutralHead headTerm)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (headTerminates : IsStronglyNormalizing headTerm)
    (firstArgumentTerminates : IsStronglyNormalizing firstArgumentTerm)
    (secondArgumentTerminates : IsStronglyNormalizing secondArgumentTerm) :
    IsStronglyNormalizing
      (applyRawArgumentsFrom headTerm
        [firstArgumentTerm, secondArgumentTerm]) :=
  applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_arguments
    (isNeutralHead := isNeutralHead)
    headIsNeutral
    neutralHeadIsNotLambda
    neutralHeadStep
    headTerminates
    (AllStronglyNormalizingArguments.cons firstArgumentTerminates
      (AllStronglyNormalizingArguments.cons secondArgumentTerminates
        AllStronglyNormalizingArguments.nil))

/-- Three-argument specialization of the finite neutral-spine accessibility
helper.  This is the selected-branch shape used by list-cons eliminators:
`app (app (app neutralHead firstArgument) secondArgument) thirdArgument`. -/
theorem applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_three_arguments
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {headTerm firstArgumentTerm secondArgumentTerm thirdArgumentTerm :
      RawTerm scope}
    (headIsNeutral : isNeutralHead headTerm)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (headTerminates : IsStronglyNormalizing headTerm)
    (firstArgumentTerminates : IsStronglyNormalizing firstArgumentTerm)
    (secondArgumentTerminates : IsStronglyNormalizing secondArgumentTerm)
    (thirdArgumentTerminates : IsStronglyNormalizing thirdArgumentTerm) :
    IsStronglyNormalizing
      (applyRawArgumentsFrom headTerm
        [firstArgumentTerm, secondArgumentTerm, thirdArgumentTerm]) :=
  applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_arguments
    (isNeutralHead := isNeutralHead)
    headIsNeutral
    neutralHeadIsNotLambda
    neutralHeadStep
    headTerminates
    (AllStronglyNormalizingArguments.cons firstArgumentTerminates
      (AllStronglyNormalizingArguments.cons secondArgumentTerminates
        (AllStronglyNormalizingArguments.cons thirdArgumentTerminates
          AllStronglyNormalizingArguments.nil)))

/-- Folding more arguments onto a variable-headed spine preserves the
variable-headed-spine invariant. -/
theorem variableHeadedSpineTermFrom_isVariableHeadedSpine {scope : Nat}
    {headIndex : Fin scope} {headTerm : RawTerm scope}
    (headIsVariableSpine : IsVariableHeadedSpine headIndex headTerm)
    (argumentTerms : List (RawTerm scope)) :
    IsVariableHeadedSpine headIndex
      (variableHeadedSpineTermFrom headTerm argumentTerms) := by
  induction argumentTerms generalizing headTerm with
  | nil =>
      exact headIsVariableSpine
  | cons argumentTerm remainingArguments inductionHypothesis =>
      exact inductionHypothesis
        (IsVariableHeadedSpine.applyArgument headIsVariableSpine)

/-- Folding arguments onto a variable head produces a variable-headed spine. -/
theorem variableHeadedSpineTerm_isVariableHeadedSpine {scope : Nat}
    (headIndex : Fin scope) (argumentTerms : List (RawTerm scope)) :
    IsVariableHeadedSpine headIndex
      (variableHeadedSpineTerm headIndex argumentTerms) :=
  variableHeadedSpineTermFrom_isVariableHeadedSpine
    (IsVariableHeadedSpine.rootVariable (headIndex := headIndex))
    argumentTerms

/-- Any finite variable-headed spine is strongly normalizing when its initial
head is a strongly-normalizing variable-headed spine and every added argument
is strongly normalizing. -/
theorem variableHeadedSpineTermFrom_isStronglyNormalizing_of_arguments
    {scope : Nat} {headIndex : Fin scope} {headTerm : RawTerm scope}
    {argumentTerms : List (RawTerm scope)}
    (headIsVariableSpine : IsVariableHeadedSpine headIndex headTerm)
    (headTerminates : IsStronglyNormalizing headTerm)
    (argumentTermsTerminate :
      AllStronglyNormalizingArguments argumentTerms) :
    IsStronglyNormalizing
      (variableHeadedSpineTermFrom headTerm argumentTerms) :=
  applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_arguments
    (isNeutralHead := IsVariableHeadedSpine headIndex)
    headIsVariableSpine
    (fun variableSpineHead lambdaDomain lambdaBody =>
      isVariableHeadedSpine_not_lam variableSpineHead lambdaDomain lambdaBody)
    (fun variableSpineHead variableSpineStep =>
      isVariableHeadedSpine_step variableSpineHead variableSpineStep)
    headTerminates
    argumentTermsTerminate

/-- Any finite application spine rooted at a variable is strongly normalizing
when every argument is strongly normalizing. -/
theorem variableHeadedSpineTerm_isStronglyNormalizing_of_arguments
    {scope : Nat} (headIndex : Fin scope)
    {argumentTerms : List (RawTerm scope)}
    (argumentTermsTerminate :
      AllStronglyNormalizingArguments argumentTerms) :
    IsStronglyNormalizing
      (variableHeadedSpineTerm headIndex argumentTerms) :=
  variableHeadedSpineTermFrom_isStronglyNormalizing_of_arguments
    (headIndex := headIndex)
    (headTerm := .mkGen .gen_var headIndex .childNil)
    (IsVariableHeadedSpine.rootVariable (headIndex := headIndex))
    (var_isStronglyNormalizing headIndex)
    argumentTermsTerminate

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
      ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
        headTerm ≠ .mkGen .gen_lam ()
          (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
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
              obtain ⟨lambdaDomain, lambdaBody, headEq, _⟩ := betaBranch
              exact False.elim (headIsNotLambda lambdaDomain lambdaBody headEq)
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
    (fun lambdaDomain lambdaBody headEq => by
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
    (neutralHeadIsNotLambda := fun candidateHeadIsNeutral lambdaDomain
        lambdaBody candidateHeadEq => by
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
          obtain ⟨lambdaDomain, lambdaBody, variableEq, _⟩ := betaBranch
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

/-- A three-argument variable-headed application spine is strongly normalizing
when all three arguments are strongly normalizing.

This is the first concrete use of the reusable neutral-application-head
extension lemma.  It remains a stuck-spine result only: beta is ruled out
because every reduct of the head is still an application spine rooted at a
variable, never a lambda. -/
theorem appVarSpine3_isStronglyNormalizing_of_arguments {scope : Nat}
    (headIndex : Fin scope)
    {firstArgument secondArgument thirdArgument : RawTerm scope}
    (firstTerminates : IsStronglyNormalizing firstArgument)
    (secondTerminates : IsStronglyNormalizing secondArgument)
    (thirdTerminates : IsStronglyNormalizing thirdArgument) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_var headIndex .childNil)
                  (.childCons firstArgument .childNil)))
              (.childCons secondArgument .childNil)))
          (.childCons thirdArgument .childNil)) :
        RawTerm scope) :=
  app_isStronglyNormalizing_of_neutral_application_head_arg
    (isNeutralHead := fun candidateHead =>
      ∃ currentFirstArgument : RawTerm scope,
        candidateHead =
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_var headIndex .childNil)
              (.childCons currentFirstArgument .childNil)) :
            RawTerm scope))
    (headIsNeutralApplication :=
      ⟨ (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_var headIndex .childNil)
            (.childCons firstArgument .childNil)) :
          RawTerm scope)
      , secondArgument
      , ⟨firstArgument, rfl⟩
      , rfl ⟩)
    (neutralHeadIsNotLambda := fun candidateHeadIsNeutral lambdaDomain
        lambdaBody candidateHeadEq => by
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
          obtain ⟨lambdaDomain, lambdaBody, variableEq, _⟩ := betaBranch
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
      appVarSpine2_isStronglyNormalizing_of_arguments headIndex
        firstTerminates secondTerminates)
    thirdTerminates

end StepStar
end FX1Poly.Core
