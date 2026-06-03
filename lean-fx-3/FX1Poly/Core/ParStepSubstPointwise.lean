import FX1Poly.Core.ParStepSubstRename
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Core/ParStepSubstPointwise
    — the parallel substitution lemma and its diagonal corollary (the #420 triangle's β/ι engine).

`ParStepSubstRename.lean` shipped `ParStep.subst` (one fixed substitution applied to both sides) and
`ParStep.rename`.  The Takahashi triangle `ParStep a b → ParStep b (completeDevelopment a)` needs more
at its β/ι arms: when the source β-redex `(λ body) arg` fires to `subst0 body arg` and BOTH the body
and the argument have themselves parallel-reduced, the reduct must parallel-reduce to the contractum
built from the developed components.  That is the **diagonal** substitution lemma
`ParStep b b' → ParStep a a' → ParStep (subst0 b a) (subst0 b' a')` — vary the term AND the argument
simultaneously.  Because `ParStep` is a single parallel step (NOT transitive), this cannot be obtained
by composing two one-sided `ParStep.subst` applications; it requires the combined induction.

* `ParStep.weaken` — `ParStep` under the weakening renaming; corollary of `ParStep.subst` via
  `weaken_eq_subst_weaken`, mirroring `StepStar.weaken`.
* `RawTermSubst.PointwiseParStep` — two substitutions related entrywise by `ParStep`; `lift_pointwiseParStep`
  / `iterateLiftRaw_..._pointwiseParStep` lift the relation under binders (var 0 reflexive, the weakened
  tail by `ParStep.weaken`).
* `ParStep.substPointwise` / `ParStepChildren.substPointwise` — the combined lemma: pointwise-related
  substitutions applied across a `ParStep` yield a `ParStep`.  Same `ParStep.rec` recursor as
  `ParStep.subst` but the motive carries two substitutions `σ τ` and their `PointwiseParStep` witness; β
  lifts both via `subst0_subst_commute`, the cong variable case is exactly the pointwise hypothesis at the
  variable's index, every ι arm threads `(σ, τ, pw)` to its premises' IHs, and the spine iterate-lifts both.
* `ParStep.subst0_diagonal` — the diagonal corollary, `ParStep.substPointwise` instantiated at the two
  `singleton` substitutions (`subst0 body arg` is reducibly `subst (singleton arg) body`); the
  `singleton`s are pointwise-related because var 0 carries `argStep` and higher variables are identical.

## Zero-axiom verification

`weaken`/`substPointwise` reduce to `ParStep.subst` + the recursor; the lift helpers are `match` on the
de Bruijn index + `ParStep.weaken`/`refl`; the diagonal is a direct instantiation.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **`ParStep` is stable under the weakening renaming.**  Corollary of `ParStep.subst`: rewrite
`RawTerm.weaken` as `subst` by the weakening renaming (`weaken_eq_subst_weaken`), mirroring
`StepStar.weaken`. -/
theorem ParStep.weaken {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (sourceParStep : ParStep sourceTerm targetTerm) :
    ParStep (RawTerm.weaken sourceTerm) (RawTerm.weaken targetTerm) := by
  rw [RawTerm.weaken_eq_subst_weaken sourceTerm, RawTerm.weaken_eq_subst_weaken targetTerm]
  exact ParStep.subst
    (RawRenaming.thenSubst RawRenaming.weaken (RawTermSubst.identity (scope := scope + 1)))
    sourceParStep

/-- Two substitutions are **pointwise-ParStep-related** when each entry parallel-reduces. -/
def RawTermSubst.PointwiseParStep {sourceScope targetScope : Nat}
    (first second : RawTermSubst sourceScope targetScope) : Prop :=
  ∀ position, ParStep (first position) (second position)

/-- Lifting through one binder preserves pointwise ParStep relatedness: var 0 is reflexive, the
weakened tail steps by `ParStep.weaken`. -/
theorem RawTermSubst.lift_pointwiseParStep {sourceScope targetScope : Nat}
    {first second : RawTermSubst sourceScope targetScope}
    (relatedness : RawTermSubst.PointwiseParStep first second) :
    RawTermSubst.PointwiseParStep first.lift second.lift := by
  intro position
  match position with
  | ⟨0, _⟩ => exact ParStep.refl _
  | ⟨priorPositionValue + 1, positionBound⟩ =>
      show ParStep
        (RawTerm.weaken (first ⟨priorPositionValue, Nat.lt_of_succ_lt_succ positionBound⟩))
        (RawTerm.weaken (second ⟨priorPositionValue, Nat.lt_of_succ_lt_succ positionBound⟩))
      exact ParStep.weaken
        (relatedness ⟨priorPositionValue, Nat.lt_of_succ_lt_succ positionBound⟩)

/-- Iterated binder lift preserves pointwise ParStep relatedness. -/
theorem iterateLiftRaw_RawTermSubst_pointwiseParStep {sourceScope targetScope : Nat}
    {first second : RawTermSubst sourceScope targetScope}
    (relatedness : RawTermSubst.PointwiseParStep first second)
    (binderDepth : Nat) :
    RawTermSubst.PointwiseParStep
      (iterateLiftRaw first binderDepth) (iterateLiftRaw second binderDepth) := by
  induction binderDepth with
  | zero => exact relatedness
  | succ priorDepth priorIH => exact RawTermSubst.lift_pointwiseParStep priorIH

/-- **Parallel substitution lemma.**  Pointwise-ParStep-related substitutions applied across a `ParStep`
yield a `ParStep` — varying BOTH the substitution (`sigma ⇒ tau`) AND the term (`source ⇒ target`).
The `ParStep.rec` recursor with the two-substitution motive: β lifts both substitutions
(`subst0_subst_commute` + `lift_pointwiseParStep`), the cong variable case is the pointwise hypothesis at
the variable's index, every ι arm threads `(sigma, tau, relatedness)` to its premises' IHs, and the
children spine iterate-lifts both substitutions by the child binder shift. -/
theorem ParStep.substPointwise {sourceScope targetScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (sourceParStep : ParStep sourceTerm targetTerm)
    (sigma tau : RawTermSubst sourceScope targetScope)
    (relatedness : RawTermSubst.PointwiseParStep sigma tau) :
    ParStep (RawTerm.subst sigma sourceTerm) (RawTerm.subst tau targetTerm) := by
  let motiveStep :
      {scope : Nat} → (first second : RawTerm scope) → ParStep first second → Prop :=
    fun {scope} first second _ =>
      ∀ {targetScope : Nat}, (sigma tau : RawTermSubst scope targetScope) →
        RawTermSubst.PointwiseParStep sigma tau →
        ParStep (RawTerm.subst sigma first) (RawTerm.subst tau second)
  let motiveChildren :
      {parentScope : Nat} → {binderShifts : List Nat} →
        (first second : RawTermChildren binderShifts parentScope) →
        ParStepChildren first second → Prop :=
    fun {parentScope} {_} first second _ =>
      ∀ {targetScope : Nat}, (sigma tau : RawTermSubst parentScope targetScope) →
        RawTermSubst.PointwiseParStep sigma tau →
        ParStepChildren (RawTermChildren.subst sigma first)
          (RawTermChildren.subst tau second)
  exact
    (ParStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {scope} {body body' arg arg'} _bodyStep _argStep ihBody ihArg
          {targetScope} sigma tau pw => by
        rw [RawTerm.subst0_subst_commute]
        exact ParStep.beta
          (ihBody (RawTermSubst.lift sigma) (RawTermSubst.lift tau)
            (RawTermSubst.lift_pointwiseParStep pw))
          (ihArg sigma tau pw))
      (fun {scope} generator payload {children children'} _childrenStep ihChildren
          {targetScope} sigma tau pw => by
        by_cases hVar : generator = .gen_var
        · subst hVar
          cases _childrenStep
          show ParStep (sigma payload) (tau payload)
          exact pw payload
        · rw [RawTerm.subst_nonVar_reduces sigma hVar payload children]
          rw [RawTerm.subst_nonVar_reduces tau hVar payload children']
          exact ParStep.cong generator _ (ihChildren sigma tau pw))
      (fun {scope} {thenBranch thenBranch' elseBranch} _step ihThen {targetScope} sigma tau pw =>
        ParStep.iotaBoolTrue (ihThen sigma tau pw))
      (fun {scope} {thenBranch elseBranch elseBranch'} _step ihElse {targetScope} sigma tau pw =>
        ParStep.iotaBoolFalse (ihElse sigma tau pw))
      (fun {scope} {firstValue firstValue' secondValue} _step ihFirst {targetScope} sigma tau pw =>
        ParStep.iotaFstPair (ihFirst sigma tau pw))
      (fun {scope} {firstValue secondValue secondValue'} _step ihSecond {targetScope} sigma tau pw =>
        ParStep.iotaSndPair (ihSecond sigma tau pw))
      (fun {scope} {zeroBranch zeroBranch' succBranch} _step ihZero {targetScope} sigma tau pw =>
        ParStep.iotaNatElimZero (ihZero sigma tau pw))
      (fun {scope} {zeroBranch zeroBranch' succBranch} _step ihZero {targetScope} sigma tau pw =>
        ParStep.iotaNatRecZero (ihZero sigma tau pw))
      (fun {scope} {nilBranch nilBranch' consBranch} _step ihNil {targetScope} sigma tau pw =>
        ParStep.iotaListElimNil (ihNil sigma tau pw))
      (fun {scope} {noneBranch noneBranch' someBranch} _step ihNone {targetScope} sigma tau pw =>
        ParStep.iotaOptionMatchNone (ihNone sigma tau pw))
      (fun {scope} {value value' noneBranch someBranch someBranch'} _stepSome _stepVal
          ihSome ihVal {targetScope} sigma tau pw =>
        ParStep.iotaOptionMatchSome (ihSome sigma tau pw) (ihVal sigma tau pw))
      (fun {scope} {value value' leftBranch leftBranch' rightBranch} _stepLeft _stepVal
          ihLeft ihVal {targetScope} sigma tau pw =>
        ParStep.iotaEitherMatchInl (ihLeft sigma tau pw) (ihVal sigma tau pw))
      (fun {scope} {value value' leftBranch rightBranch rightBranch'} _stepRight _stepVal
          ihRight ihVal {targetScope} sigma tau pw =>
        ParStep.iotaEitherMatchInr (ihRight sigma tau pw) (ihVal sigma tau pw))
      (fun {scope} {predecessor predecessor' zeroBranch zeroBranch' succBranch succBranch'}
          _stepPred _stepZero _stepSucc ihPred ihZero ihSucc {targetScope} sigma tau pw =>
        ParStep.iotaNatElimSucc (ihPred sigma tau pw) (ihZero sigma tau pw) (ihSucc sigma tau pw))
      (fun {scope} {predecessor predecessor' zeroBranch zeroBranch' succBranch succBranch'}
          _stepPred _stepZero _stepSucc ihPred ihZero ihSucc {targetScope} sigma tau pw =>
        ParStep.iotaNatRecSucc (ihPred sigma tau pw) (ihZero sigma tau pw) (ihSucc sigma tau pw))
      (fun {scope} {headVal headVal' tailVal tailVal' nilBranch nilBranch' consBranch consBranch'}
          _stepHead _stepTail _stepNil _stepCons ihHead ihTail ihNil ihCons
          {targetScope} sigma tau pw =>
        ParStep.iotaListElimCons (ihHead sigma tau pw) (ihTail sigma tau pw)
          (ihNil sigma tau pw) (ihCons sigma tau pw))
      (fun {scope} {baseCase baseCase' rawWitness} _step ihBase {targetScope} sigma tau pw =>
        ParStep.iotaIdJRefl (ihBase sigma tau pw))
      (fun {scope} {baseCase baseCase' rawWitness} _step ihBase {targetScope} sigma tau pw =>
        ParStep.iotaIdStrictRecRefl (ihBase sigma tau pw))
      (fun {scope} {targetScope} sigma tau pw => ParStepChildren.nil)
      (fun {parentScope} {headShift} {restShifts} {childHead childHead' childTail childTail'}
          _headStep _tailStep ihHead ihTail {targetScope} sigma tau pw =>
        ParStepChildren.cons
          (ihHead (iterateLiftRaw sigma headShift) (iterateLiftRaw tau headShift)
            (iterateLiftRaw_RawTermSubst_pointwiseParStep pw headShift))
          (ihTail sigma tau pw))
      sourceParStep)
      sigma tau relatedness

/-- The `singleton` substitutions for two `ParStep`-related arguments are pointwise-ParStep-related: var 0
carries the argument step, higher variables are identical (`ParStep.refl`). -/
theorem RawTermSubst.singleton_pointwiseParStep {scope : Nat} {arg arg' : RawTerm scope}
    (argStep : ParStep arg arg') :
    RawTermSubst.PointwiseParStep (RawTermSubst.singleton arg) (RawTermSubst.singleton arg') := by
  intro position
  match position with
  | ⟨0, _⟩ => exact argStep
  | ⟨_ + 1, _⟩ => exact ParStep.refl _

/-- **Diagonal parallel substitution.**  Substituting a parallel-reduced argument into a parallel-reduced
body parallel-reduces.  `ParStep.substPointwise` at the two `singleton` substitutions (`subst0 body arg`
is reducibly `subst (singleton arg) body`).  This is the engine the triangle's β arm fires with — and
the recursive ι arms, whose contractums embed `subst0` of the developed components. -/
theorem ParStep.subst0_diagonal {scope : Nat} {body body' : RawTerm (scope + 1)}
    {arg arg' : RawTerm scope}
    (bodyStep : ParStep body body') (argStep : ParStep arg arg') :
    ParStep (RawTerm.subst0 body arg) (RawTerm.subst0 body' arg') :=
  ParStep.substPointwise bodyStep (RawTermSubst.singleton arg) (RawTermSubst.singleton arg')
    (RawTermSubst.singleton_pointwiseParStep argStep)

end FX1Poly.Core
