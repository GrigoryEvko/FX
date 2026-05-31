import FX1Poly.Core.StepStarConfluence

/-! # Foundation/PolyCell/Core/StrongNormalizationApplication
    — strong normalization projects through an application cell

If an application cell `app f a` (`gen_app` over function `f` and argument `a`) is strongly
normalizing, then so are both children `f` and `a`.  The PROJECTION direction (cell SN ⇒ child SN),
dual to the constructor direction (`StrongNormalizationConstructors`: child SN ⇒ cell SN under the
no-root-redex hypothesis).

## Why this lemma (the arrow candidate's CR1)

It is the sub-lemma the arrow reducibility candidate's CR1 consumes (polycell.md §11.8.5, the Tait
machinery): from `app t u : B` reducible (hence SN) for a fresh argument variable `u`, CR1 must
recover `SN t`.  A single child step lifts FORWARD to a cell step (`Step.cong` + `StepChildren.here`
for the function, `StepChildren.there ∘ here` for the argument), so the cell's accessibility transfers
down to each child — the `Acc` induction is generalised over the cell so the recursion's index is a
variable, exactly as `isStronglyNormalizing_of_rename` does for the renaming reflection.

## Zero-axiom verification

`Acc` induction generalised over the application cell + the `Step.cong`/`StepChildren` forward lift —
no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept by
`#audit_namespace FX1Poly.Core` in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- SN projects to the FUNCTION child of an application: if `app function argument` is strongly
normalizing then so is `function`.  Each function step lifts forward to a cell step
(`Step.cong .gen_app () (StepChildren.here _ functionStep)`), so the cell's accessibility transfers to
the function.  The `Acc` induction is generalised over the application cell so the recursion's index is
a variable. -/
theorem isStronglyNormalizing_app_function {scope : Nat} {function argument : RawTerm scope}
    (applicationTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))) :
    IsStronglyNormalizing function := by
  suffices general :
      ∀ {applicationWitness : RawTerm scope}, Acc StepSuccessor applicationWitness →
        ∀ {currentFunction currentArgument : RawTerm scope},
          applicationWitness =
            .mkGen .gen_app ()
              (.childCons currentFunction (.childCons currentArgument .childNil)) →
          Acc StepSuccessor currentFunction from
    general applicationTerminates rfl
  intro applicationWitness applicationAccessible
  induction applicationAccessible with
  | intro applicationFocus _applicationPredecessors applicationInductiveHypothesis =>
      intro currentFunction currentArgument witnessEq
      subst witnessEq
      apply Acc.intro
      intro functionAfter functionStep
      have applicationStep :
          Step
            (.mkGen .gen_app ()
              (.childCons currentFunction (.childCons currentArgument .childNil)))
            (.mkGen .gen_app ()
              (.childCons functionAfter (.childCons currentArgument .childNil))) :=
        Step.cong .gen_app () (StepChildren.here _ functionStep)
      exact applicationInductiveHypothesis _ applicationStep rfl

/-- SN projects to the ARGUMENT child of an application: if `app function argument` is strongly
normalizing then so is `argument`.  The argument step lifts through the tail of the spine
(`StepChildren.there _ (StepChildren.here _ argumentStep)`), so the cell's accessibility transfers to
the argument.  The Σ-of-the-projection-pair the arrow candidate completes with. -/
theorem isStronglyNormalizing_app_argument {scope : Nat} {function argument : RawTerm scope}
    (applicationTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))) :
    IsStronglyNormalizing argument := by
  suffices general :
      ∀ {applicationWitness : RawTerm scope}, Acc StepSuccessor applicationWitness →
        ∀ {currentFunction currentArgument : RawTerm scope},
          applicationWitness =
            .mkGen .gen_app ()
              (.childCons currentFunction (.childCons currentArgument .childNil)) →
          Acc StepSuccessor currentArgument from
    general applicationTerminates rfl
  intro applicationWitness applicationAccessible
  induction applicationAccessible with
  | intro applicationFocus _applicationPredecessors applicationInductiveHypothesis =>
      intro currentFunction currentArgument witnessEq
      subst witnessEq
      apply Acc.intro
      intro argumentAfter argumentStep
      have applicationStep :
          Step
            (.mkGen .gen_app ()
              (.childCons currentFunction (.childCons currentArgument .childNil)))
            (.mkGen .gen_app ()
              (.childCons currentFunction (.childCons argumentAfter .childNil))) :=
        Step.cong .gen_app ()
          (StepChildren.there _ (StepChildren.here _ argumentStep))
      exact applicationInductiveHypothesis _ applicationStep rfl

end StepStar
end FX1Poly.Core
