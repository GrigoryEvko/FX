import LeanFX2.Foundation.PolyCell.Core.StepStar
import LeanFX2.Foundation.PolyCell.Core.RawTermSubst0Commute
import LeanFX2.Foundation.PolyCell.Core.StructuralInductionPrimitives

/-! # Foundation/PolyCell/Core/StepSubst

Substitution compatibility for one-step reduction on the v2 raw
substrate.

The load-bearing case is beta: after an outer substitution, the beta
contractum is reshaped by `RawTerm.subst0_subst_commute`, so the
substituted redex still contracts in one `Step`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- One-step reduction is stable under raw substitution. -/
theorem Step.subst {sourceScope targetScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (sigma : RawTermSubst sourceScope targetScope)
    (sourceStep : Step sourceTerm targetTerm) :
    Step (RawTerm.subst sigma sourceTerm) (RawTerm.subst sigma targetTerm) := by
  let motiveStep :
      {scope : Nat} → (first second : RawTerm scope) →
        Step first second → Prop :=
    fun {scope} first second _ =>
      ∀ {targetScope : Nat}, (subst : RawTermSubst scope targetScope) →
        Step (RawTerm.subst subst first) (RawTerm.subst subst second)
  let motiveChildren :
      {parentScope : Nat} → {binderShifts : List Nat} →
        (first second : RawTermChildren binderShifts parentScope) →
        StepChildren first second → Prop :=
    fun {parentScope} {_} first second _ =>
      ∀ {targetScope : Nat}, (subst : RawTermSubst parentScope targetScope) →
        StepChildren (RawTermChildren.subst subst first)
          (RawTermChildren.subst subst second)
  exact
    (Step.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {scope} {body} {arg} {targetScope} sigma => by
        rw [RawTerm.subst0_subst_commute]
        exact Step.beta)
      (fun {scope} generator payload {children} {children'} childStep
          childStepSubst {targetScope} sigma => by
        by_cases hVar : generator = .gen_var
        · subst hVar
          cases childStep
        · rw [RawTerm.subst_nonVar_reduces sigma hVar payload children]
          rw [RawTerm.subst_nonVar_reduces sigma hVar payload children']
          exact Step.cong generator _ (childStepSubst sigma))
      (fun {scope} {thenBranch} {elseBranch} {targetScope} sigma =>
        Step.iotaBoolTrue)
      (fun {scope} {thenBranch} {elseBranch} {targetScope} sigma =>
        Step.iotaBoolFalse)
      (fun {scope} {firstValue} {secondValue} {targetScope} sigma =>
        Step.iotaFstPair)
      (fun {scope} {firstValue} {secondValue} {targetScope} sigma =>
        Step.iotaSndPair)
      (fun {scope} {zeroBranch} {succBranch} {targetScope} sigma =>
        Step.iotaNatElimZero)
      (fun {scope} {zeroBranch} {succBranch} {targetScope} sigma =>
        Step.iotaNatRecZero)
      (fun {scope} {nilBranch} {consBranch} {targetScope} sigma =>
        Step.iotaListElimNil)
      (fun {scope} {noneBranch} {someBranch} {targetScope} sigma =>
        Step.iotaOptionMatchNone)
      (fun {scope} {value} {noneBranch} {someBranch} {targetScope} sigma =>
        Step.iotaOptionMatchSome)
      (fun {scope} {value} {leftBranch} {rightBranch} {targetScope} sigma =>
        Step.iotaEitherMatchInl)
      (fun {scope} {value} {leftBranch} {rightBranch} {targetScope} sigma =>
        Step.iotaEitherMatchInr)
      (fun {scope} {predecessor} {zeroBranch} {succBranch} {targetScope}
          sigma => Step.iotaNatElimSucc)
      (fun {scope} {predecessor} {zeroBranch} {succBranch} {targetScope}
          sigma => Step.iotaNatRecSucc)
      (fun {scope} {headVal} {tailVal} {nilBranch} {consBranch}
          {targetScope} sigma => Step.iotaListElimCons)
      (fun {scope} {baseCase} {rawWitness} {targetScope} sigma =>
        Step.iotaIdJRefl)
      (fun {scope} {baseCase} {rawWitness} {targetScope} sigma =>
        Step.iotaIdStrictRecRefl)
      (fun {parentScope} {headShift} {restShifts} {head} {head'} rest
          childStep childStepSubst {targetScope} sigma =>
        StepChildren.here
          (RawTermChildren.subst sigma rest)
          (childStepSubst (iterateLiftRaw sigma headShift)))
      (fun {parentScope} {headShift} {restShifts} head {rest} {rest'}
          restStep restStepSubst {targetScope} sigma =>
        StepChildren.there
          (RawTerm.subst (iterateLiftRaw sigma headShift) head)
          (restStepSubst sigma))
      sourceStep)
      sigma

/-- Child-spine one-step reduction is stable under raw substitution. -/
theorem StepChildren.subst {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    {sourceChildren targetChildren :
      RawTermChildren binderShifts parentSourceScope}
    (sigma : RawTermSubst parentSourceScope parentTargetScope)
    (childrenStep : StepChildren sourceChildren targetChildren) :
    StepChildren (RawTermChildren.subst sigma sourceChildren)
      (RawTermChildren.subst sigma targetChildren) := by
  let motiveStep :
      {scope : Nat} → (first second : RawTerm scope) →
        Step first second → Prop :=
    fun {scope} first second _ =>
      ∀ {targetScope : Nat}, (subst : RawTermSubst scope targetScope) →
        Step (RawTerm.subst subst first) (RawTerm.subst subst second)
  let motiveChildren :
      {parentScope : Nat} → {binderShifts : List Nat} →
        (first second : RawTermChildren binderShifts parentScope) →
        StepChildren first second → Prop :=
    fun {parentScope} {_} first second _ =>
      ∀ {targetScope : Nat}, (subst : RawTermSubst parentScope targetScope) →
        StepChildren (RawTermChildren.subst subst first)
          (RawTermChildren.subst subst second)
  exact
    (StepChildren.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {scope} {body} {arg} {targetScope} sigma => by
        rw [RawTerm.subst0_subst_commute]
        exact Step.beta)
      (fun {scope} generator payload {children} {children'} childStep
          childStepSubst {targetScope} sigma => by
        by_cases hVar : generator = .gen_var
        · subst hVar
          cases childStep
        · rw [RawTerm.subst_nonVar_reduces sigma hVar payload children]
          rw [RawTerm.subst_nonVar_reduces sigma hVar payload children']
          exact Step.cong generator _ (childStepSubst sigma))
      (fun {scope} {thenBranch} {elseBranch} {targetScope} sigma =>
        Step.iotaBoolTrue)
      (fun {scope} {thenBranch} {elseBranch} {targetScope} sigma =>
        Step.iotaBoolFalse)
      (fun {scope} {firstValue} {secondValue} {targetScope} sigma =>
        Step.iotaFstPair)
      (fun {scope} {firstValue} {secondValue} {targetScope} sigma =>
        Step.iotaSndPair)
      (fun {scope} {zeroBranch} {succBranch} {targetScope} sigma =>
        Step.iotaNatElimZero)
      (fun {scope} {zeroBranch} {succBranch} {targetScope} sigma =>
        Step.iotaNatRecZero)
      (fun {scope} {nilBranch} {consBranch} {targetScope} sigma =>
        Step.iotaListElimNil)
      (fun {scope} {noneBranch} {someBranch} {targetScope} sigma =>
        Step.iotaOptionMatchNone)
      (fun {scope} {value} {noneBranch} {someBranch} {targetScope} sigma =>
        Step.iotaOptionMatchSome)
      (fun {scope} {value} {leftBranch} {rightBranch} {targetScope} sigma =>
        Step.iotaEitherMatchInl)
      (fun {scope} {value} {leftBranch} {rightBranch} {targetScope} sigma =>
        Step.iotaEitherMatchInr)
      (fun {scope} {predecessor} {zeroBranch} {succBranch} {targetScope}
          sigma => Step.iotaNatElimSucc)
      (fun {scope} {predecessor} {zeroBranch} {succBranch} {targetScope}
          sigma => Step.iotaNatRecSucc)
      (fun {scope} {headVal} {tailVal} {nilBranch} {consBranch}
          {targetScope} sigma => Step.iotaListElimCons)
      (fun {scope} {baseCase} {rawWitness} {targetScope} sigma =>
        Step.iotaIdJRefl)
      (fun {scope} {baseCase} {rawWitness} {targetScope} sigma =>
        Step.iotaIdStrictRecRefl)
      (fun {parentScope} {headShift} {restShifts} {head} {head'} rest
          childStep childStepSubst {targetScope} sigma =>
        StepChildren.here
          (RawTermChildren.subst sigma rest)
          (childStepSubst (iterateLiftRaw sigma headShift)))
      (fun {parentScope} {headShift} {restShifts} head {rest} {rest'}
          restStep restStepSubst {targetScope} sigma =>
        StepChildren.there
          (RawTerm.subst (iterateLiftRaw sigma headShift) head)
          (restStepSubst sigma))
      childrenStep)
      sigma

/-- Substitute every term in a `StepStar` chain. -/
theorem StepStar.subst {sourceScope targetScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (sigma : RawTermSubst sourceScope targetScope)
    (sourceChain : StepStar sourceTerm targetTerm) :
    StepStar (RawTerm.subst sigma sourceTerm)
      (RawTerm.subst sigma targetTerm) := by
  induction sourceChain with
  | refl _ =>
      exact StepStar.refl _
  | trans headStep _ tailIH =>
      exact StepStar.trans (Step.subst sigma headStep) tailIH

/-- Weakening is substitution by the canonical variable-shift
substitution. -/
theorem RawTerm.weaken_eq_subst_weaken {scope : Nat}
    (sourceTerm : RawTerm scope) :
    RawTerm.weaken sourceTerm =
      RawTerm.subst
        (RawRenaming.thenSubst RawRenaming.weaken
          (RawTermSubst.identity (scope := scope + 1)))
        sourceTerm := by
  rw [RawTerm.weaken_eq_rename]
  have renameThenIdentity :=
    RawTerm.rename_subst_commute RawRenaming.weaken
      (RawTermSubst.identity (scope := scope + 1)) sourceTerm
  rw [RawTerm.subst_identity_apply] at renameThenIdentity
  exact renameThenIdentity

/-- Weaken a single reduction step through one fresh raw binder. -/
theorem Step.weaken {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (sourceStep : Step sourceTerm targetTerm) :
    Step (RawTerm.weaken sourceTerm) (RawTerm.weaken targetTerm) := by
  rw [RawTerm.weaken_eq_subst_weaken sourceTerm,
    RawTerm.weaken_eq_subst_weaken targetTerm]
  exact Step.subst
    (RawRenaming.thenSubst RawRenaming.weaken
      (RawTermSubst.identity (scope := scope + 1)))
    sourceStep

/-- Weaken every term in a `StepStar` chain. -/
theorem StepStar.weaken {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (sourceChain : StepStar sourceTerm targetTerm) :
    StepStar (RawTerm.weaken sourceTerm) (RawTerm.weaken targetTerm) := by
  rw [RawTerm.weaken_eq_subst_weaken sourceTerm,
    RawTerm.weaken_eq_subst_weaken targetTerm]
  exact StepStar.subst
    (RawRenaming.thenSubst RawRenaming.weaken
      (RawTermSubst.identity (scope := scope + 1)))
    sourceChain

/-- Pointwise `StepStar` relation between two raw substitutions. -/
def RawTermSubst.PointwiseStepStar {sourceScope targetScope : Nat}
    (firstSubstitution secondSubstitution :
      RawTermSubst sourceScope targetScope) : Prop :=
  ∀ position, StepStar (firstSubstitution position)
    (secondSubstitution position)

/-- Lifting substitutions through one binder preserves pointwise
`StepStar` relatedness. -/
theorem RawTermSubst.lift_pointwiseStepStar
    {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
      RawTermSubst sourceScope targetScope}
    (substitutionStep :
      RawTermSubst.PointwiseStepStar firstSubstitution
        secondSubstitution) :
    RawTermSubst.PointwiseStepStar firstSubstitution.lift
      secondSubstitution.lift := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      exact StepStar.refl _
  | ⟨priorPositionValue + 1, positionBound⟩ =>
      show StepStar
        (RawTerm.weaken
          (firstSubstitution
            ⟨priorPositionValue,
              Nat.lt_of_succ_lt_succ positionBound⟩))
        (RawTerm.weaken
          (secondSubstitution
            ⟨priorPositionValue,
              Nat.lt_of_succ_lt_succ positionBound⟩))
      exact StepStar.weaken
        (substitutionStep
          ⟨priorPositionValue,
            Nat.lt_of_succ_lt_succ positionBound⟩)

/-- Iterated binder lift preserves pointwise `StepStar` relatedness. -/
theorem iterateLiftRaw_RawTermSubst_pointwiseStepStar
    {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
      RawTermSubst sourceScope targetScope}
    (substitutionStep :
      RawTermSubst.PointwiseStepStar firstSubstitution
        secondSubstitution)
    (binderDepth : Nat) :
    RawTermSubst.PointwiseStepStar
      (iterateLiftRaw firstSubstitution binderDepth)
      (iterateLiftRaw secondSubstitution binderDepth) := by
  induction binderDepth with
  | zero =>
      exact substitutionStep
  | succ priorDepth priorIH =>
      exact RawTermSubst.lift_pointwiseStepStar priorIH

/-- Reflexive-transitive closure of one-step child-spine reduction. -/
inductive StepChildrenStar {binderShifts : List Nat} {scope : Nat} :
    RawTermChildren binderShifts scope →
    RawTermChildren binderShifts scope → Prop where
  | refl (children : RawTermChildren binderShifts scope) :
      StepChildrenStar children children
  | trans {firstChildren secondChildren thirdChildren :
        RawTermChildren binderShifts scope} :
      StepChildren firstChildren secondChildren →
      StepChildrenStar secondChildren thirdChildren →
      StepChildrenStar firstChildren thirdChildren

namespace StepChildrenStar

/-- Compose two child-spine `StepChildrenStar` chains. -/
theorem trans_compose {binderShifts : List Nat} {scope : Nat}
    {firstChildren secondChildren thirdChildren :
      RawTermChildren binderShifts scope}
    (firstChain : StepChildrenStar firstChildren secondChildren)
    (secondChain : StepChildrenStar secondChildren thirdChildren) :
    StepChildrenStar firstChildren thirdChildren := by
  induction firstChain with
  | refl _ =>
      exact secondChain
  | trans headStep _ tailIH =>
      exact StepChildrenStar.trans headStep (tailIH secondChain)

/-- Replay a term `StepStar` chain in the head of a child spine. -/
theorem here {scope shift : Nat} {restShifts : List Nat}
    {sourceHead targetHead : RawTerm (scope + shift)}
    (restChildren : RawTermChildren restShifts scope)
    (headChain : StepStar sourceHead targetHead) :
    StepChildrenStar
      (RawTermChildren.childCons sourceHead restChildren)
      (RawTermChildren.childCons targetHead restChildren) := by
  induction headChain with
  | refl _ =>
      exact StepChildrenStar.refl _
  | trans headStep _ tailIH =>
      exact StepChildrenStar.trans
        (StepChildren.here restChildren headStep)
        tailIH

/-- Replay a child-spine chain in the tail of a larger child spine. -/
theorem there {scope shift : Nat} {restShifts : List Nat}
    (head : RawTerm (scope + shift))
    {sourceTail targetTail : RawTermChildren restShifts scope}
    (tailChain : StepChildrenStar sourceTail targetTail) :
    StepChildrenStar
      (RawTermChildren.childCons head sourceTail)
      (RawTermChildren.childCons head targetTail) := by
  induction tailChain with
  | refl _ =>
      exact StepChildrenStar.refl _
  | trans headStep _ tailIH =>
      exact StepChildrenStar.trans
        (StepChildren.there head headStep)
        tailIH

end StepChildrenStar

/-- Lift a child-spine `StepChildrenStar` chain through a generator
congruence context. -/
theorem StepStar.ofChildrenStar {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {sourceChildren targetChildren :
      RawTermChildren generator.binderShifts scope}
    (childrenChain : StepChildrenStar sourceChildren targetChildren) :
    StepStar (.mkGen generator payload sourceChildren)
      (.mkGen generator payload targetChildren) := by
  induction childrenChain with
  | refl _ =>
      exact StepStar.refl _
  | trans headStep _ tailIH =>
      exact StepStar.trans (Step.cong generator payload headStep) tailIH

mutual

/-- Pointwise `StepStar`-related substitutions replay through raw
substitution on a term. -/
theorem RawTerm.subst_pointwise_stepStar {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
      RawTermSubst sourceScope targetScope}
    (substitutionStep :
      RawTermSubst.PointwiseStepStar firstSubstitution secondSubstitution)
    (sourceTerm : RawTerm sourceScope) :
    StepStar (RawTerm.subst firstSubstitution sourceTerm)
      (RawTerm.subst secondSubstitution sourceTerm) := by
  match sourceTerm with
  | .mkGen generator payload children =>
    by_cases hVar : generator = .gen_var
    · subst hVar
      cases children with
      | childNil =>
          show StepStar
            (firstSubstitution payload) (secondSubstitution payload)
          exact substitutionStep payload
    · rw [RawTerm.subst_nonVar_reduces
        firstSubstitution hVar payload children]
      rw [RawTerm.subst_nonVar_reduces
        secondSubstitution hVar payload children]
      exact StepStar.ofChildrenStar
        (RawTermChildren.subst_pointwise_stepStar substitutionStep children)

/-- Pointwise `StepStar`-related substitutions replay through raw
substitution on a child spine. -/
theorem RawTermChildren.subst_pointwise_stepStar
    {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
      RawTermSubst sourceScope targetScope}
    (substitutionStep :
      RawTermSubst.PointwiseStepStar firstSubstitution secondSubstitution)
    {binderShifts : List Nat}
    (children : RawTermChildren binderShifts sourceScope) :
    StepChildrenStar
      (RawTermChildren.subst firstSubstitution children)
      (RawTermChildren.subst secondSubstitution children) := by
  match binderShifts, children with
  | [], .childNil =>
      exact StepChildrenStar.refl _
  | headShift :: _, .childCons childHead childTail =>
      show StepChildrenStar
        (RawTermChildren.childCons
          (RawTerm.subst
            (iterateLiftRaw firstSubstitution headShift) childHead)
          (RawTermChildren.subst firstSubstitution childTail))
        (RawTermChildren.childCons
          (RawTerm.subst
            (iterateLiftRaw secondSubstitution headShift) childHead)
          (RawTermChildren.subst secondSubstitution childTail))
      have headChain :=
        RawTerm.subst_pointwise_stepStar
          (iterateLiftRaw_RawTermSubst_pointwiseStepStar
            substitutionStep headShift)
          childHead
      have tailChain :=
        RawTermChildren.subst_pointwise_stepStar
          substitutionStep childTail
      exact StepChildrenStar.trans_compose
        (StepChildrenStar.here
          (RawTermChildren.subst firstSubstitution childTail)
          headChain)
        (StepChildrenStar.there
          (RawTerm.subst
            (iterateLiftRaw secondSubstitution headShift) childHead)
          tailChain)

end

/-- Replay a body step through `subst0` with a fixed argument.

This is the beta/function-congruence replay: if the lambda body steps,
then the beta contractum steps after substituting the same argument. -/
theorem Step.subst0Body {scope : Nat}
    {body updatedBody : RawTerm (scope + 1)}
    (argument : RawTerm scope) (bodyStep : Step body updatedBody) :
    StepStar (RawTerm.subst0 body argument)
      (RawTerm.subst0 updatedBody argument) :=
  StepStar.single (Step.subst (RawTermSubst.singleton argument) bodyStep)

/-- Replay an argument step through `subst0` with a fixed body.

This is the beta/argument-congruence replay.  Unlike the function case,
the body may duplicate variable 0, so the result is a `StepStar` chain
obtained by replaying a pointwise substitution relation through the
body's structure. -/
theorem Step.subst0Argument {scope : Nat}
    (body : RawTerm (scope + 1))
    {argument updatedArgument : RawTerm scope}
    (argumentStep : Step argument updatedArgument) :
    StepStar (RawTerm.subst0 body argument)
      (RawTerm.subst0 body updatedArgument) := by
  apply RawTerm.subst_pointwise_stepStar
  intro position
  cases position with
  | mk positionValue positionBound =>
      cases positionValue with
      | zero =>
          exact StepStar.single argumentStep
      | succ priorPositionValue =>
          exact StepStar.refl _

end LeanFX2.Foundation.PolyCell.Core
