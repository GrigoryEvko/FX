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

/-- Replay a body step through `subst0` with a fixed argument.

This is the beta/function-congruence replay: if the lambda body steps,
then the beta contractum steps after substituting the same argument. -/
theorem Step.subst0Body {scope : Nat}
    {body updatedBody : RawTerm (scope + 1)}
    (argument : RawTerm scope) (bodyStep : Step body updatedBody) :
    StepStar (RawTerm.subst0 body argument)
      (RawTerm.subst0 updatedBody argument) :=
  StepStar.single (Step.subst (RawTermSubst.singleton argument) bodyStep)

end LeanFX2.Foundation.PolyCell.Core
