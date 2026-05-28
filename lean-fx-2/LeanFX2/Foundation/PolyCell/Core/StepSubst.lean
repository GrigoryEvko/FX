import LeanFX2.Foundation.PolyCell.Core.StepStar
import LeanFX2.Foundation.PolyCell.Core.RawTermSubst0Commute
import LeanFX2.Foundation.PolyCell.Core.RawTermFresh
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

/-- Replay a step out of a weakened term by substituting any closed
source-scope unit term for the fresh variable.

This is the source-step half of the future weaken-step inversion lemma:
it derives a genuine source-scope `Step` from
`Step (RawTerm.weaken sourceTerm) targetTerm`.  The remaining freshness
half is proving that `targetTerm` is itself a weakening image, i.e. that
`RawTerm.strengthen targetTerm` succeeds with this same substituted
target. -/
theorem Step.weaken_substTarget {scope : Nat}
    {sourceTerm : RawTerm scope}
    {targetTerm : RawTerm (scope + 1)}
    (underBinderStep : Step (RawTerm.weaken sourceTerm) targetTerm) :
    Step sourceTerm
      (RawTerm.subst
        (RawTermSubst.singleton
          (.mkGen .gen_unit () .childNil : RawTerm scope))
        targetTerm) := by
  let unitTerm : RawTerm scope := .mkGen .gen_unit () .childNil
  have substitutedStep :=
    Step.subst (RawTermSubst.singleton unitTerm) underBinderStep
  rw [RawTerm.weaken_subst_singleton sourceTerm unitTerm] at substitutedStep
  exact substitutedStep

/-- Child-spine sibling of `Step.weaken_substTarget`.

This replays a child-spine step out of a weakened children spine by
substituting a canonical source-scope unit term for the fresh variable. -/
theorem StepChildren.weaken_substTarget {scope : Nat}
    {binderShifts : List Nat}
    {sourceChildren : RawTermChildren binderShifts scope}
    {targetChildren : RawTermChildren binderShifts (scope + 1)}
    (underBinderStep :
      StepChildren (RawTermChildren.weaken sourceChildren) targetChildren) :
    StepChildren sourceChildren
      (RawTermChildren.subst
        (RawTermSubst.singleton
          (.mkGen .gen_unit () .childNil : RawTerm scope))
        targetChildren) := by
  let unitTerm : RawTerm scope := .mkGen .gen_unit () .childNil
  have substitutedStep :=
    StepChildren.subst (RawTermSubst.singleton unitTerm) underBinderStep
  rw [RawTermChildren.weaken_subst_singleton sourceChildren unitTerm]
    at substitutedStep
  dsimp only [unitTerm] at substitutedStep
  exact substitutedStep

/-- One-step reduction preserves any substitution/renaming retraction
freshness proof.

The eta-critical-pair use case specializes this to `weaken` after
singleton substitution: if a term under a fresh binder reduces, the reduct
is still fresh for that binder. -/
theorem Step.preserves_isFreshFor {sourceScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (sourceStep : Step sourceTerm targetTerm) :
    ∀ {targetScope : Nat}
      (rawRenaming : RawRenaming targetScope sourceScope)
      (rawSubstitution : RawTermSubst sourceScope targetScope),
      RawTerm.isFreshFor rawRenaming rawSubstitution sourceTerm →
      RawTerm.isFreshFor rawRenaming rawSubstitution targetTerm := by
  intro targetScope rawRenaming rawSubstitution sourceFresh
  let motiveStep :
      {scope : Nat} → (firstTerm secondTerm : RawTerm scope) →
        Step firstTerm secondTerm → Prop :=
    fun {scope} firstTerm secondTerm _ =>
      ∀ {targetScope : Nat}
        (rawRenaming : RawRenaming targetScope scope)
        (rawSubstitution : RawTermSubst scope targetScope),
        RawTerm.isFreshFor rawRenaming rawSubstitution firstTerm →
        RawTerm.isFreshFor rawRenaming rawSubstitution secondTerm
  let motiveChildren :
      {parentScope : Nat} → {binderShifts : List Nat} →
        (firstChildren secondChildren :
          RawTermChildren binderShifts parentScope) →
        StepChildren firstChildren secondChildren → Prop :=
    fun {parentScope} {_} firstChildren secondChildren _ =>
      ∀ {targetScope : Nat}
        (rawRenaming : RawRenaming targetScope parentScope)
        (rawSubstitution : RawTermSubst parentScope targetScope),
        RawTermChildren.isFreshFor rawRenaming rawSubstitution
          firstChildren →
        RawTermChildren.isFreshFor rawRenaming rawSubstitution
          secondChildren
  exact
    (Step.rec (motive_1 := motiveStep) (motive_2 := motiveChildren)
      (fun {scope} {body} {arg} {targetScope} rawRenaming rawSubstitution
          sourceFresh => by
        let appChildren :=
          ((.childCons
              (.mkGen .gen_lam () (.childCons body .childNil))
              (.childCons arg .childNil)) : RawTermChildren [0, 0] scope)
        have appChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              appChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_app) rawRenaming rawSubstitution
            (by decide) () appChildren sourceFresh
        have lamFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_lam () (.childCons body .childNil) :
                RawTerm scope) :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ appChildrenFresh
        have argumentSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons arg .childNil) : RawTermChildren [0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ appChildrenFresh
        have argFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution arg :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ argumentSpineFresh
        have lamChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons body .childNil) : RawTermChildren [1] scope) :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_lam) rawRenaming rawSubstitution
            (by decide) () _ lamFresh
        have bodyFresh :
            RawTerm.isFreshFor (RawRenaming.lift rawRenaming)
              (RawTermSubst.lift rawSubstitution) body :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ lamChildrenFresh
        unfold RawTerm.isFreshFor
        rw [RawTerm.subst0_subst_commute]
        rw [RawTerm.rename_subst0_commute]
        unfold RawTerm.isFreshFor at bodyFresh
        unfold RawTerm.isFreshFor at argFresh
        rw [bodyFresh, argFresh])
      (fun {scope} generator payload {children} {children'} childStep
          childFreshIH {targetScope} rawRenaming rawSubstitution
          sourceFresh => by
        by_cases generatorIsVar : generator = .gen_var
        · subst generatorIsVar
          cases childStep
        · have childrenFresh :
              RawTermChildren.isFreshFor rawRenaming rawSubstitution
                children :=
            RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
              rawRenaming rawSubstitution generatorIsVar payload children
              sourceFresh
          exact RawTerm.isFreshFor_nonVar_of_children_isFreshFor
            rawRenaming rawSubstitution generatorIsVar payload children'
            (childFreshIH rawRenaming rawSubstitution childrenFresh))
      (fun {scope} {thenBranch} {elseBranch} {targetScope} rawRenaming
          rawSubstitution sourceFresh => by
        let sourceChildren :=
          ((.childCons (.mkGen .gen_boolTrue () .childNil)
            (.childCons thenBranch (.childCons elseBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_boolElim) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons thenBranch (.childCons elseBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        exact RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
          rawRenaming rawSubstitution _ _ branchSpineFresh)
      (fun {scope} {thenBranch} {elseBranch} {targetScope} rawRenaming
          rawSubstitution sourceFresh => by
        let sourceChildren :=
          ((.childCons (.mkGen .gen_boolFalse () .childNil)
            (.childCons thenBranch (.childCons elseBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_boolElim) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons thenBranch (.childCons elseBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have elseSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons elseBranch .childNil) :
                RawTermChildren [0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ branchSpineFresh
        exact RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
          rawRenaming rawSubstitution _ _ elseSpineFresh)
      (fun {scope} {firstValue} {secondValue} {targetScope} rawRenaming
          rawSubstitution sourceFresh => by
        let pairChildren :=
          ((.childCons firstValue (.childCons secondValue .childNil)) :
            RawTermChildren [0, 0] scope)
        let fstChildren :=
          ((.childCons (.mkGen .gen_pair () pairChildren) .childNil) :
            RawTermChildren [0] scope)
        have fstChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              fstChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_fst) rawRenaming rawSubstitution
            (by decide) () fstChildren sourceFresh
        have pairFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_pair () pairChildren : RawTerm scope) :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ fstChildrenFresh
        have pairChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              pairChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_pair) rawRenaming rawSubstitution
            (by decide) () pairChildren pairFresh
        exact RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
          rawRenaming rawSubstitution _ _ pairChildrenFresh)
      (fun {scope} {firstValue} {secondValue} {targetScope} rawRenaming
          rawSubstitution sourceFresh => by
        let pairChildren :=
          ((.childCons firstValue (.childCons secondValue .childNil)) :
            RawTermChildren [0, 0] scope)
        let sndChildren :=
          ((.childCons (.mkGen .gen_pair () pairChildren) .childNil) :
            RawTermChildren [0] scope)
        have sndChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sndChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_snd) rawRenaming rawSubstitution
            (by decide) () sndChildren sourceFresh
        have pairFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_pair () pairChildren : RawTerm scope) :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ sndChildrenFresh
        have pairChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              pairChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_pair) rawRenaming rawSubstitution
            (by decide) () pairChildren pairFresh
        have secondSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons secondValue .childNil) :
                RawTermChildren [0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ pairChildrenFresh
        exact RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
          rawRenaming rawSubstitution _ _ secondSpineFresh)
      (fun {scope} {zeroBranch} {succBranch} {targetScope} rawRenaming
          rawSubstitution sourceFresh => by
        let sourceChildren :=
          ((.childCons (.mkGen .gen_natZero () .childNil)
            (.childCons zeroBranch (.childCons succBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_natElim) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons zeroBranch (.childCons succBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        exact RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
          rawRenaming rawSubstitution _ _ branchSpineFresh)
      (fun {scope} {zeroBranch} {succBranch} {targetScope} rawRenaming
          rawSubstitution sourceFresh => by
        let sourceChildren :=
          ((.childCons (.mkGen .gen_natZero () .childNil)
            (.childCons zeroBranch (.childCons succBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_natRec) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons zeroBranch (.childCons succBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        exact RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
          rawRenaming rawSubstitution _ _ branchSpineFresh)
      (fun {scope} {nilBranch} {consBranch} {targetScope} rawRenaming
          rawSubstitution sourceFresh => by
        let sourceChildren :=
          ((.childCons (.mkGen .gen_listNil () .childNil)
            (.childCons nilBranch (.childCons consBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_listElim) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons nilBranch (.childCons consBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        exact RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
          rawRenaming rawSubstitution _ _ branchSpineFresh)
      (fun {scope} {noneBranch} {someBranch} {targetScope} rawRenaming
          rawSubstitution sourceFresh => by
        let sourceChildren :=
          ((.childCons (.mkGen .gen_optionNone () .childNil)
            (.childCons noneBranch (.childCons someBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_optionMatch) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons noneBranch (.childCons someBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        exact RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
          rawRenaming rawSubstitution _ _ branchSpineFresh)
      (fun {scope} {value} {noneBranch} {someBranch} {targetScope}
          rawRenaming rawSubstitution sourceFresh => by
        let optionSomeChildren :=
          ((.childCons value .childNil) : RawTermChildren [0] scope)
        let sourceChildren :=
          ((.childCons (.mkGen .gen_optionSome () optionSomeChildren)
            (.childCons noneBranch (.childCons someBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_optionMatch) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have optionSomeFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_optionSome () optionSomeChildren : RawTerm scope) :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have optionSomeChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              optionSomeChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_optionSome) rawRenaming rawSubstitution
            (by decide) () optionSomeChildren optionSomeFresh
        have valueFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution value :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ optionSomeChildrenFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons noneBranch (.childCons someBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have someSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons someBranch .childNil) :
                RawTermChildren [0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ branchSpineFresh
        have someBranchFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution someBranch :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ someSpineFresh
        exact RawTerm.isFreshFor_nonVar_of_children_isFreshFor
          (generator := .gen_app) rawRenaming rawSubstitution (by decide)
          () _ (RawTermChildren.double_isFreshFor
            (firstShift := 0) (secondShift := 0) rawRenaming
            rawSubstitution someBranch value someBranchFresh valueFresh))
      (fun {scope} {value} {leftBranch} {rightBranch} {targetScope}
          rawRenaming rawSubstitution sourceFresh => by
        let eitherInlChildren :=
          ((.childCons value .childNil) : RawTermChildren [0] scope)
        let sourceChildren :=
          ((.childCons (.mkGen .gen_eitherInl () eitherInlChildren)
            (.childCons leftBranch (.childCons rightBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_eitherMatch) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have eitherInlFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_eitherInl () eitherInlChildren : RawTerm scope) :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have eitherInlChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              eitherInlChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_eitherInl) rawRenaming rawSubstitution
            (by decide) () eitherInlChildren eitherInlFresh
        have valueFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution value :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ eitherInlChildrenFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons leftBranch (.childCons rightBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have leftBranchFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution leftBranch :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ branchSpineFresh
        exact RawTerm.isFreshFor_nonVar_of_children_isFreshFor
          (generator := .gen_app) rawRenaming rawSubstitution (by decide)
          () _ (RawTermChildren.double_isFreshFor
            (firstShift := 0) (secondShift := 0) rawRenaming
            rawSubstitution leftBranch value leftBranchFresh valueFresh))
      (fun {scope} {value} {leftBranch} {rightBranch} {targetScope}
          rawRenaming rawSubstitution sourceFresh => by
        let eitherInrChildren :=
          ((.childCons value .childNil) : RawTermChildren [0] scope)
        let sourceChildren :=
          ((.childCons (.mkGen .gen_eitherInr () eitherInrChildren)
            (.childCons leftBranch (.childCons rightBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_eitherMatch) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have eitherInrFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_eitherInr () eitherInrChildren : RawTerm scope) :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have eitherInrChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              eitherInrChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_eitherInr) rawRenaming rawSubstitution
            (by decide) () eitherInrChildren eitherInrFresh
        have valueFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution value :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ eitherInrChildrenFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons leftBranch (.childCons rightBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have rightBranchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons rightBranch .childNil) :
                RawTermChildren [0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ branchSpineFresh
        have rightBranchFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution rightBranch :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ rightBranchSpineFresh
        exact RawTerm.isFreshFor_nonVar_of_children_isFreshFor
          (generator := .gen_app) rawRenaming rawSubstitution (by decide)
          () _ (RawTermChildren.double_isFreshFor
            (firstShift := 0) (secondShift := 0) rawRenaming
            rawSubstitution rightBranch value rightBranchFresh valueFresh))
      (fun {scope} {predecessor} {zeroBranch} {succBranch} {targetScope}
          rawRenaming rawSubstitution sourceFresh => by
        let natSuccChildren :=
          ((.childCons predecessor .childNil) : RawTermChildren [0] scope)
        let sourceChildren :=
          ((.childCons (.mkGen .gen_natSucc () natSuccChildren)
            (.childCons zeroBranch (.childCons succBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_natElim) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have natSuccFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_natSucc () natSuccChildren : RawTerm scope) :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have natSuccChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              natSuccChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_natSucc) rawRenaming rawSubstitution
            (by decide) () natSuccChildren natSuccFresh
        have predecessorFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution predecessor :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ natSuccChildrenFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons zeroBranch (.childCons succBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have zeroBranchFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution zeroBranch :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ branchSpineFresh
        have succBranchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons succBranch .childNil) :
                RawTermChildren [0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ branchSpineFresh
        have succBranchFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution succBranch :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ succBranchSpineFresh
        have recursiveFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_natElim ()
                (.childCons predecessor
                  (.childCons zeroBranch
                    (.childCons succBranch .childNil))) : RawTerm scope) :=
          RawTerm.isFreshFor_nonVar_of_children_isFreshFor
            (generator := .gen_natElim) rawRenaming rawSubstitution
            (by decide) () _
            (RawTermChildren.triple_isFreshFor
              (firstShift := 0) (secondShift := 0) (thirdShift := 0)
              rawRenaming rawSubstitution
              predecessor zeroBranch succBranch predecessorFresh
              zeroBranchFresh succBranchFresh)
        have innerAppFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_app ()
                (.childCons succBranch (.childCons predecessor .childNil)) :
                  RawTerm scope) :=
          RawTerm.isFreshFor_nonVar_of_children_isFreshFor
            (generator := .gen_app) rawRenaming rawSubstitution
            (by decide) () _
            (RawTermChildren.double_isFreshFor
              (firstShift := 0) (secondShift := 0)
              rawRenaming rawSubstitution
              succBranch predecessor succBranchFresh predecessorFresh)
        exact RawTerm.isFreshFor_nonVar_of_children_isFreshFor
          (generator := .gen_app) rawRenaming rawSubstitution (by decide)
          () _ (RawTermChildren.double_isFreshFor
            (firstShift := 0) (secondShift := 0) rawRenaming
            rawSubstitution
            ((.mkGen .gen_app ()
              (.childCons succBranch (.childCons predecessor .childNil))) :
                RawTerm scope)
            ((.mkGen .gen_natElim ()
              (.childCons predecessor
                (.childCons zeroBranch
                  (.childCons succBranch .childNil)))) : RawTerm scope)
            innerAppFresh recursiveFresh))
      (fun {scope} {predecessor} {zeroBranch} {succBranch} {targetScope}
          rawRenaming rawSubstitution sourceFresh => by
        let natSuccChildren :=
          ((.childCons predecessor .childNil) : RawTermChildren [0] scope)
        let sourceChildren :=
          ((.childCons (.mkGen .gen_natSucc () natSuccChildren)
            (.childCons zeroBranch (.childCons succBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_natRec) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have natSuccFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_natSucc () natSuccChildren : RawTerm scope) :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have natSuccChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              natSuccChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_natSucc) rawRenaming rawSubstitution
            (by decide) () natSuccChildren natSuccFresh
        have predecessorFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution predecessor :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ natSuccChildrenFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons zeroBranch (.childCons succBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have zeroBranchFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution zeroBranch :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ branchSpineFresh
        have succBranchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons succBranch .childNil) :
                RawTermChildren [0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ branchSpineFresh
        have succBranchFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution succBranch :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ succBranchSpineFresh
        have recursiveFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_natRec ()
                (.childCons predecessor
                  (.childCons zeroBranch
                    (.childCons succBranch .childNil))) : RawTerm scope) :=
          RawTerm.isFreshFor_nonVar_of_children_isFreshFor
            (generator := .gen_natRec) rawRenaming rawSubstitution
            (by decide) () _
            (RawTermChildren.triple_isFreshFor
              (firstShift := 0) (secondShift := 0) (thirdShift := 0)
              rawRenaming rawSubstitution
              predecessor zeroBranch succBranch predecessorFresh
              zeroBranchFresh succBranchFresh)
        have innerAppFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_app ()
                (.childCons succBranch (.childCons predecessor .childNil)) :
                  RawTerm scope) :=
          RawTerm.isFreshFor_nonVar_of_children_isFreshFor
            (generator := .gen_app) rawRenaming rawSubstitution
            (by decide) () _
            (RawTermChildren.double_isFreshFor
              (firstShift := 0) (secondShift := 0)
              rawRenaming rawSubstitution
              succBranch predecessor succBranchFresh predecessorFresh)
        exact RawTerm.isFreshFor_nonVar_of_children_isFreshFor
          (generator := .gen_app) rawRenaming rawSubstitution (by decide)
          () _ (RawTermChildren.double_isFreshFor
            (firstShift := 0) (secondShift := 0) rawRenaming
            rawSubstitution
            ((.mkGen .gen_app ()
              (.childCons succBranch (.childCons predecessor .childNil))) :
                RawTerm scope)
            ((.mkGen .gen_natRec ()
              (.childCons predecessor
                (.childCons zeroBranch
                  (.childCons succBranch .childNil)))) : RawTerm scope)
            innerAppFresh recursiveFresh))
      (fun {scope} {headVal} {tailVal} {nilBranch} {consBranch}
          {targetScope} rawRenaming rawSubstitution sourceFresh => by
        let listConsChildren :=
          ((.childCons headVal (.childCons tailVal .childNil)) :
            RawTermChildren [0, 0] scope)
        let sourceChildren :=
          ((.childCons (.mkGen .gen_listCons () listConsChildren)
            (.childCons nilBranch (.childCons consBranch .childNil))) :
              RawTermChildren [0, 0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_listElim) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        have listConsFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_listCons () listConsChildren : RawTerm scope) :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have listConsChildrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              listConsChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_listCons) rawRenaming rawSubstitution
            (by decide) () listConsChildren listConsFresh
        have headFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution headVal :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ listConsChildrenFresh
        have tailSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons tailVal .childNil) :
                RawTermChildren [0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ listConsChildrenFresh
        have tailFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution tailVal :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ tailSpineFresh
        have branchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons nilBranch (.childCons consBranch .childNil)) :
                RawTermChildren [0, 0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ childrenFresh
        have nilBranchFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution nilBranch :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ branchSpineFresh
        have consBranchSpineFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              ((.childCons consBranch .childNil) :
                RawTermChildren [0] scope) :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ branchSpineFresh
        have consBranchFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution consBranch :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution _ _ consBranchSpineFresh
        have firstAppFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_app ()
                (.childCons consBranch (.childCons headVal .childNil)) :
                  RawTerm scope) :=
          RawTerm.isFreshFor_nonVar_of_children_isFreshFor
            (generator := .gen_app) rawRenaming rawSubstitution
            (by decide) () _
            (RawTermChildren.double_isFreshFor
              (firstShift := 0) (secondShift := 0)
              rawRenaming rawSubstitution
              consBranch headVal consBranchFresh headFresh)
        have secondAppFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app ()
                    (.childCons consBranch (.childCons headVal .childNil)))
                  (.childCons tailVal .childNil)) : RawTerm scope) :=
          RawTerm.isFreshFor_nonVar_of_children_isFreshFor
            (generator := .gen_app) rawRenaming rawSubstitution
            (by decide) () _
            (RawTermChildren.double_isFreshFor
              (firstShift := 0) (secondShift := 0)
              rawRenaming rawSubstitution
              ((.mkGen .gen_app ()
                (.childCons consBranch (.childCons headVal .childNil))) :
                  RawTerm scope)
              tailVal firstAppFresh tailFresh)
        have recursiveFresh :
            RawTerm.isFreshFor rawRenaming rawSubstitution
              (.mkGen .gen_listElim ()
                (.childCons tailVal
                  (.childCons nilBranch
                    (.childCons consBranch .childNil))) : RawTerm scope) :=
          RawTerm.isFreshFor_nonVar_of_children_isFreshFor
            (generator := .gen_listElim) rawRenaming rawSubstitution
            (by decide) () _
            (RawTermChildren.triple_isFreshFor
              (firstShift := 0) (secondShift := 0) (thirdShift := 0)
              rawRenaming rawSubstitution
              tailVal nilBranch consBranch tailFresh nilBranchFresh
              consBranchFresh)
        exact RawTerm.isFreshFor_nonVar_of_children_isFreshFor
          (generator := .gen_app) rawRenaming rawSubstitution (by decide)
          () _ (RawTermChildren.double_isFreshFor
            (firstShift := 0) (secondShift := 0) rawRenaming
            rawSubstitution
            ((.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app ()
                  (.childCons consBranch (.childCons headVal .childNil)))
                (.childCons tailVal .childNil))) : RawTerm scope)
            ((.mkGen .gen_listElim ()
              (.childCons tailVal
                (.childCons nilBranch
                  (.childCons consBranch .childNil)))) : RawTerm scope)
            secondAppFresh recursiveFresh))
      (fun {scope} {baseCase} {rawWitness} {targetScope} rawRenaming
          rawSubstitution sourceFresh => by
        let sourceChildren :=
          ((.childCons baseCase
            (.childCons
              (.mkGen .gen_refl ()
                (.childCons rawWitness .childNil))
              .childNil)) : RawTermChildren [0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_idJ) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        exact RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
          rawRenaming rawSubstitution _ _ childrenFresh)
      (fun {scope} {baseCase} {rawWitness} {targetScope} rawRenaming
          rawSubstitution sourceFresh => by
        let sourceChildren :=
          ((.childCons baseCase
            (.childCons
              (.mkGen .gen_refl ()
                (.childCons rawWitness .childNil))
              .childNil)) : RawTermChildren [0, 0] scope)
        have childrenFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution
              sourceChildren :=
          RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
            (generator := .gen_idStrictRec) rawRenaming rawSubstitution
            (by decide) () sourceChildren sourceFresh
        exact RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
          rawRenaming rawSubstitution _ _ childrenFresh)
      (fun {parentScope} {headShift} {restShifts} {head} {head'} rest
          _childStep childFreshIH {targetScope} rawRenaming rawSubstitution
          sourceFresh => by
        have headFresh :
            RawTerm.isFreshFor (iterateLiftRaw rawRenaming headShift)
              (iterateLiftRaw rawSubstitution headShift) head :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution head rest sourceFresh
        have tailFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution rest :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution head rest sourceFresh
        exact RawTermChildren.childCons_isFreshFor rawRenaming
          rawSubstitution head' rest
          (childFreshIH (iterateLiftRaw rawRenaming headShift)
            (iterateLiftRaw rawSubstitution headShift) headFresh)
          tailFresh)
      (fun {parentScope} {headShift} {restShifts} head {rest} {rest'}
          _restStep restFreshIH {targetScope} rawRenaming rawSubstitution
          sourceFresh => by
        have headFresh :
            RawTerm.isFreshFor (iterateLiftRaw rawRenaming headShift)
              (iterateLiftRaw rawSubstitution headShift) head :=
          RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution head rest sourceFresh
        have tailFresh :
            RawTermChildren.isFreshFor rawRenaming rawSubstitution rest :=
          RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
            rawRenaming rawSubstitution head rest sourceFresh
        exact RawTermChildren.childCons_isFreshFor rawRenaming
          rawSubstitution head rest' headFresh
          (restFreshIH rawRenaming rawSubstitution tailFresh))
      sourceStep)
      rawRenaming rawSubstitution sourceFresh

/-- A reduct of a weakened source term strengthens to the same term obtained
by substituting a canonical source-scope unit for the fresh variable. -/
theorem Step.weaken_strengthenTarget {scope : Nat}
    {sourceTerm : RawTerm scope}
    {targetTerm : RawTerm (scope + 1)}
    (underBinderStep : Step (RawTerm.weaken sourceTerm) targetTerm) :
    RawTerm.strengthen targetTerm =
      some (RawTerm.subst
        (RawTermSubst.singleton
          (.mkGen .gen_unit () .childNil : RawTerm scope))
        targetTerm) := by
  let unitTerm : RawTerm scope := .mkGen .gen_unit () .childNil
  have sourceFresh :
      RawTerm.isFreshFor RawRenaming.weaken
        (RawTermSubst.singleton unitTerm) (RawTerm.weaken sourceTerm) := by
    unfold RawTerm.isFreshFor
    rw [RawTerm.weaken_subst_singleton sourceTerm unitTerm]
    rw [RawTerm.weaken_eq_rename sourceTerm]
  exact RawTerm.strengthen_eq_subst_of_isFreshFor_singleton
    unitTerm targetTerm
    (Step.preserves_isFreshFor underBinderStep RawRenaming.weaken
      (RawTermSubst.singleton unitTerm) sourceFresh)

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
