import FX1Poly.Core.ParallelReduction
import FX1Poly.Core.StepSubst
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Core/ParStepSubstRename
    — parallel reduction is stable under substitution and renaming.

`ParallelReduction.lean` defines `ParStep` (Takahashi parallel reduction) and the shipped sandwich
`Step ⊆ ParStep ⊆ StepStar`.  The remaining obligation for unconditional raw confluence is the
`ParStep` diamond, which `TakahashiTriangle.lean` reduces to the one-sided triangle
`ParStep a b → ParStep b (completeDevelopment a)`.  That triangle's β/ι arms need the **parallel
substitution lemma** — substituting a parallel-reduced argument into a parallel-reduced body parallel-
reduces — whose binder case in turn needs `ParStep` closed under renaming (to lift a parallel
substitution under a binder).  This file ships the two foundational substrate lemmas those depend on:

* `ParStep.subst` / `ParStepChildren.subst` — `ParStep` is stable under applying a fixed substitution to
  both sides.  Proved by the `ParStep.rec` recursor with the "generalize over all substitutions" motive
  (`∀ σ, ParStep (subst σ first) (subst σ second)`), exactly the `Step.subst` idiom: β via
  `subst0_subst_commute` (the lift is `RawTermSubst.lift`), cong via the `gen_var` split +
  `subst_nonVar_reduces`, every ι arm applies its premises' IHs at σ (the surviving sub-terms reduce in
  parallel; `subst` reduces definitionally on the concrete redex generators so the matching `ParStep`
  constructor fires), and the children spine lifts σ by the child's binder shift.
* `ParStep.rename` / `ParStepChildren.rename` — corollaries via the `Step.rename` trick: rewrite each
  side's `rename ρ` as `subst (ρ then identity)` (`rename_subst_commute` + `subst_identity_apply`), then
  apply `ParStep.subst`.

## Zero-axiom verification

`subst` is the explicit recursor application (β `rw` + the ι/cong constructors); `rename` is `rw` of the
rename→subst commutation + `ParStep.subst`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Parallel reduction is stable under a fixed substitution.**  Applying `sigma` to both sides of a
`ParStep` yields a `ParStep`.  The `ParStep.rec` recursor with the all-substitutions motive: β uses
`subst0_subst_commute` (lift `RawTermSubst.lift`), cong splits on `gen_var` (the variable case is
reflexivity after the empty spine forces both children to `childNil`) and otherwise reduces via
`subst_nonVar_reduces`, and every ι arm applies its premises' IHs at `sigma`. -/
theorem ParStep.subst {sourceScope targetScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (sigma : RawTermSubst sourceScope targetScope)
    (sourceParStep : ParStep sourceTerm targetTerm) :
    ParStep (RawTerm.subst sigma sourceTerm) (RawTerm.subst sigma targetTerm) := by
  let motiveStep :
      {scope : Nat} → (first second : RawTerm scope) → ParStep first second → Prop :=
    fun {scope} first second _ =>
      ∀ {targetScope : Nat}, (subst : RawTermSubst scope targetScope) →
        ParStep (RawTerm.subst subst first) (RawTerm.subst subst second)
  let motiveChildren :
      {parentScope : Nat} → {binderShifts : List Nat} →
        (first second : RawTermChildren binderShifts parentScope) →
        ParStepChildren first second → Prop :=
    fun {parentScope} {_} first second _ =>
      ∀ {targetScope : Nat}, (subst : RawTermSubst parentScope targetScope) →
        ParStepChildren (RawTermChildren.subst subst first)
          (RawTermChildren.subst subst second)
  exact
    (ParStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {scope} {body body' arg arg'} _bodyStep _argStep ihBody ihArg {targetScope} sigma => by
        rw [RawTerm.subst0_subst_commute]
        exact ParStep.beta (ihBody (RawTermSubst.lift sigma)) (ihArg sigma))
      (fun {scope} generator payload {children children'} _childrenStep ihChildren
          {targetScope} sigma => by
        by_cases hVar : generator = .gen_var
        · subst hVar
          cases _childrenStep
          exact ParStep.refl _
        · rw [RawTerm.subst_nonVar_reduces sigma hVar payload children]
          rw [RawTerm.subst_nonVar_reduces sigma hVar payload children']
          exact ParStep.cong generator _ (ihChildren sigma))
      (fun {scope} {thenBranch thenBranch' elseBranch} _step ihThen {targetScope} sigma =>
        ParStep.iotaBoolTrue (ihThen sigma))
      (fun {scope} {thenBranch elseBranch elseBranch'} _step ihElse {targetScope} sigma =>
        ParStep.iotaBoolFalse (ihElse sigma))
      (fun {scope} {firstValue firstValue' secondValue} _step ihFirst {targetScope} sigma =>
        ParStep.iotaFstPair (ihFirst sigma))
      (fun {scope} {firstValue secondValue secondValue'} _step ihSecond {targetScope} sigma =>
        ParStep.iotaSndPair (ihSecond sigma))
      (fun {scope} {zeroBranch zeroBranch' succBranch} _step ihZero {targetScope} sigma =>
        ParStep.iotaNatElimZero (ihZero sigma))
      (fun {scope} {zeroBranch zeroBranch' succBranch} _step ihZero {targetScope} sigma =>
        ParStep.iotaNatRecZero (ihZero sigma))
      (fun {scope} {nilBranch nilBranch' consBranch} _step ihNil {targetScope} sigma =>
        ParStep.iotaListElimNil (ihNil sigma))
      (fun {scope} {noneBranch noneBranch' someBranch} _step ihNone {targetScope} sigma =>
        ParStep.iotaOptionMatchNone (ihNone sigma))
      (fun {scope} {value value' noneBranch someBranch someBranch'} _stepSome _stepVal
          ihSome ihVal {targetScope} sigma =>
        ParStep.iotaOptionMatchSome (ihSome sigma) (ihVal sigma))
      (fun {scope} {value value' leftBranch leftBranch' rightBranch} _stepLeft _stepVal
          ihLeft ihVal {targetScope} sigma =>
        ParStep.iotaEitherMatchInl (ihLeft sigma) (ihVal sigma))
      (fun {scope} {value value' leftBranch rightBranch rightBranch'} _stepRight _stepVal
          ihRight ihVal {targetScope} sigma =>
        ParStep.iotaEitherMatchInr (ihRight sigma) (ihVal sigma))
      (fun {scope} {predecessor predecessor' zeroBranch zeroBranch' succBranch succBranch'}
          _stepPred _stepZero _stepSucc ihPred ihZero ihSucc {targetScope} sigma =>
        ParStep.iotaNatElimSucc (ihPred sigma) (ihZero sigma) (ihSucc sigma))
      (fun {scope} {predecessor predecessor' zeroBranch zeroBranch' succBranch succBranch'}
          _stepPred _stepZero _stepSucc ihPred ihZero ihSucc {targetScope} sigma =>
        ParStep.iotaNatRecSucc (ihPred sigma) (ihZero sigma) (ihSucc sigma))
      (fun {scope} {headVal headVal' tailVal tailVal' nilBranch nilBranch' consBranch consBranch'}
          _stepHead _stepTail _stepNil _stepCons ihHead ihTail ihNil ihCons {targetScope} sigma =>
        ParStep.iotaListElimCons (ihHead sigma) (ihTail sigma) (ihNil sigma) (ihCons sigma))
      (fun {scope} {baseCase baseCase' rawWitness} _step ihBase {targetScope} sigma =>
        ParStep.iotaIdJRefl (ihBase sigma))
      (fun {scope} {baseCase baseCase' rawWitness} _step ihBase {targetScope} sigma =>
        ParStep.iotaIdStrictRecRefl (ihBase sigma))
      (fun {scope} {targetScope} sigma => ParStepChildren.nil)
      (fun {parentScope} {headShift} {restShifts} {childHead childHead' childTail childTail'}
          _headStep _tailStep ihHead ihTail {targetScope} sigma =>
        ParStepChildren.cons (ihHead (iterateLiftRaw sigma headShift)) (ihTail sigma))
      sourceParStep)
      sigma

/-- **Pointwise parallel reduction of a children spine is stable under a fixed substitution** — the
children-spine companion of `ParStep.subst`, same recursor body entered at the spine derivation. -/
theorem ParStepChildren.subst {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    {sourceChildren targetChildren : RawTermChildren binderShifts parentSourceScope}
    (sigma : RawTermSubst parentSourceScope parentTargetScope)
    (childrenParStep : ParStepChildren sourceChildren targetChildren) :
    ParStepChildren (RawTermChildren.subst sigma sourceChildren)
      (RawTermChildren.subst sigma targetChildren) := by
  let motiveStep :
      {scope : Nat} → (first second : RawTerm scope) → ParStep first second → Prop :=
    fun {scope} first second _ =>
      ∀ {targetScope : Nat}, (subst : RawTermSubst scope targetScope) →
        ParStep (RawTerm.subst subst first) (RawTerm.subst subst second)
  let motiveChildren :
      {parentScope : Nat} → {binderShifts : List Nat} →
        (first second : RawTermChildren binderShifts parentScope) →
        ParStepChildren first second → Prop :=
    fun {parentScope} {_} first second _ =>
      ∀ {targetScope : Nat}, (subst : RawTermSubst parentScope targetScope) →
        ParStepChildren (RawTermChildren.subst subst first)
          (RawTermChildren.subst subst second)
  exact
    (ParStepChildren.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {scope} {body body' arg arg'} _bodyStep _argStep ihBody ihArg {targetScope} sigma => by
        rw [RawTerm.subst0_subst_commute]
        exact ParStep.beta (ihBody (RawTermSubst.lift sigma)) (ihArg sigma))
      (fun {scope} generator payload {children children'} _childrenStep ihChildren
          {targetScope} sigma => by
        by_cases hVar : generator = .gen_var
        · subst hVar
          cases _childrenStep
          exact ParStep.refl _
        · rw [RawTerm.subst_nonVar_reduces sigma hVar payload children]
          rw [RawTerm.subst_nonVar_reduces sigma hVar payload children']
          exact ParStep.cong generator _ (ihChildren sigma))
      (fun {scope} {thenBranch thenBranch' elseBranch} _step ihThen {targetScope} sigma =>
        ParStep.iotaBoolTrue (ihThen sigma))
      (fun {scope} {thenBranch elseBranch elseBranch'} _step ihElse {targetScope} sigma =>
        ParStep.iotaBoolFalse (ihElse sigma))
      (fun {scope} {firstValue firstValue' secondValue} _step ihFirst {targetScope} sigma =>
        ParStep.iotaFstPair (ihFirst sigma))
      (fun {scope} {firstValue secondValue secondValue'} _step ihSecond {targetScope} sigma =>
        ParStep.iotaSndPair (ihSecond sigma))
      (fun {scope} {zeroBranch zeroBranch' succBranch} _step ihZero {targetScope} sigma =>
        ParStep.iotaNatElimZero (ihZero sigma))
      (fun {scope} {zeroBranch zeroBranch' succBranch} _step ihZero {targetScope} sigma =>
        ParStep.iotaNatRecZero (ihZero sigma))
      (fun {scope} {nilBranch nilBranch' consBranch} _step ihNil {targetScope} sigma =>
        ParStep.iotaListElimNil (ihNil sigma))
      (fun {scope} {noneBranch noneBranch' someBranch} _step ihNone {targetScope} sigma =>
        ParStep.iotaOptionMatchNone (ihNone sigma))
      (fun {scope} {value value' noneBranch someBranch someBranch'} _stepSome _stepVal
          ihSome ihVal {targetScope} sigma =>
        ParStep.iotaOptionMatchSome (ihSome sigma) (ihVal sigma))
      (fun {scope} {value value' leftBranch leftBranch' rightBranch} _stepLeft _stepVal
          ihLeft ihVal {targetScope} sigma =>
        ParStep.iotaEitherMatchInl (ihLeft sigma) (ihVal sigma))
      (fun {scope} {value value' leftBranch rightBranch rightBranch'} _stepRight _stepVal
          ihRight ihVal {targetScope} sigma =>
        ParStep.iotaEitherMatchInr (ihRight sigma) (ihVal sigma))
      (fun {scope} {predecessor predecessor' zeroBranch zeroBranch' succBranch succBranch'}
          _stepPred _stepZero _stepSucc ihPred ihZero ihSucc {targetScope} sigma =>
        ParStep.iotaNatElimSucc (ihPred sigma) (ihZero sigma) (ihSucc sigma))
      (fun {scope} {predecessor predecessor' zeroBranch zeroBranch' succBranch succBranch'}
          _stepPred _stepZero _stepSucc ihPred ihZero ihSucc {targetScope} sigma =>
        ParStep.iotaNatRecSucc (ihPred sigma) (ihZero sigma) (ihSucc sigma))
      (fun {scope} {headVal headVal' tailVal tailVal' nilBranch nilBranch' consBranch consBranch'}
          _stepHead _stepTail _stepNil _stepCons ihHead ihTail ihNil ihCons {targetScope} sigma =>
        ParStep.iotaListElimCons (ihHead sigma) (ihTail sigma) (ihNil sigma) (ihCons sigma))
      (fun {scope} {baseCase baseCase' rawWitness} _step ihBase {targetScope} sigma =>
        ParStep.iotaIdJRefl (ihBase sigma))
      (fun {scope} {baseCase baseCase' rawWitness} _step ihBase {targetScope} sigma =>
        ParStep.iotaIdStrictRecRefl (ihBase sigma))
      (fun {scope} {targetScope} sigma => ParStepChildren.nil)
      (fun {parentScope} {headShift} {restShifts} {childHead childHead' childTail childTail'}
          _headStep _tailStep ihHead ihTail {targetScope} sigma =>
        ParStepChildren.cons (ihHead (iterateLiftRaw sigma headShift)) (ihTail sigma))
      childrenParStep)
      sigma

/-- **Parallel reduction is stable under raw renaming.**  Corollary of `ParStep.subst` via the
`Step.rename` trick: each side's `rename ρ` is `subst (ρ then identity)` (`rename_subst_commute` +
`subst_identity_apply`), so the renamed `ParStep` is a substituted one. -/
theorem ParStep.rename {sourceScope targetScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (sourceParStep : ParStep sourceTerm targetTerm) :
    ParStep (RawTerm.rename rawRenaming sourceTerm)
      (RawTerm.rename rawRenaming targetTerm) := by
  have sourceRenameAsSubst :=
    RawTerm.rename_subst_commute rawRenaming
      (RawTermSubst.identity (scope := targetScope)) sourceTerm
  have targetRenameAsSubst :=
    RawTerm.rename_subst_commute rawRenaming
      (RawTermSubst.identity (scope := targetScope)) targetTerm
  rw [RawTerm.subst_identity_apply] at sourceRenameAsSubst
  rw [RawTerm.subst_identity_apply] at targetRenameAsSubst
  rw [sourceRenameAsSubst, targetRenameAsSubst]
  exact ParStep.subst
    (RawRenaming.thenSubst rawRenaming
      (RawTermSubst.identity (scope := targetScope)))
    sourceParStep

/-- **Pointwise children-spine parallel reduction is stable under raw renaming** — the children-spine
companion of `ParStep.rename`, same rename→subst reduction over `ParStepChildren.subst`. -/
theorem ParStepChildren.rename {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    {sourceChildren targetChildren : RawTermChildren binderShifts parentSourceScope}
    (rawRenaming : RawRenaming parentSourceScope parentTargetScope)
    (childrenParStep : ParStepChildren sourceChildren targetChildren) :
    ParStepChildren (RawTermChildren.rename rawRenaming sourceChildren)
      (RawTermChildren.rename rawRenaming targetChildren) := by
  have sourceRenameAsSubst :=
    RawTermChildren.rename_subst_commute rawRenaming
      (RawTermSubst.identity (scope := parentTargetScope)) sourceChildren
  have targetRenameAsSubst :=
    RawTermChildren.rename_subst_commute rawRenaming
      (RawTermSubst.identity (scope := parentTargetScope)) targetChildren
  rw [RawTermChildren.subst_identity_apply] at sourceRenameAsSubst
  rw [RawTermChildren.subst_identity_apply] at targetRenameAsSubst
  rw [sourceRenameAsSubst, targetRenameAsSubst]
  exact ParStepChildren.subst
    (RawRenaming.thenSubst rawRenaming
      (RawTermSubst.identity (scope := parentTargetScope)))
    childrenParStep

end FX1Poly.Core
