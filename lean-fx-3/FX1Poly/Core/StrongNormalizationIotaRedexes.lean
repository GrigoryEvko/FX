import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/StrongNormalizationIotaRedexes
    — SN closure for iota-reducing eliminator redexes

The redex file ships the beta (`appLam`) SN closures.  This file opens the
parallel iota line: eliminator-rooted redexes whose root reduct is an
ι-rule.  The template is identical to `appLam`'s normal-body closure —
induct on the single child that fires the root redex (the *scrutinee*),
invert the root `Step`, and discharge {ι-fire → contractum SN; scrutinee
congruence → IH; passive-child congruence → passivity}.

This is still not global SN, not the reducibility predicate, and not the
fundamental theorem.  It is the next audited bridge: from beta-redex
accessibility into iota-redex accessibility, one eliminator at a time
(`boolElim` first; the data eliminators follow the same template).
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- A `boolElim`-headed redex is strongly normalizing when both branches are
already normal and the scrutinee is strongly normalizing.

The branches are passive: requiring them normal discharges their congruence
branches (an ι-fire lands on a branch, which is SN by `isStronglyNormalizing_of_noStep`).
The scrutinee is active: accessibility induction on it handles both the
ι-fire (`boolTrue`/`boolFalse` selecting a normal branch) and scrutinee
congruence.  Mirrors `appLam_isStronglyNormalizing_of_normal_body_contractum`
with the scrutinee in the argument role and the branches in the body role. -/
theorem boolElim_isStronglyNormalizing_of_normal_branches
    {scope : Nat} {scrutinee thenBranch elseBranch : RawTerm scope}
    (thenBranchHasNoStep :
      ∀ targetThen : RawTerm scope, Step thenBranch targetThen → False)
    (elseBranchHasNoStep :
      ∀ targetElse : RawTerm scope, Step elseBranch targetElse → False)
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_boolElim ()
        (.childCons scrutinee
          (.childCons thenBranch (.childCons elseBranch .childNil))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_boolElim ()
          (.childCons currentScrutinee
            (.childCons thenBranch (.childCons elseBranch .childNil))) :
          RawTerm scope))
    (m := fun currentScrutinee _currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_boolElim ()
          (.childCons currentScrutinee
            (.childCons thenBranch (.childCons elseBranch .childNil))) :
          RawTerm scope)
        (fun targetTerm boolElimStep => by
          cases Step.from_boolElim boolElimStep with
          | inl iotaTrueBranch =>
              obtain ⟨_scrutineeIsTrue, targetIsThen⟩ := iotaTrueBranch
              rw [targetIsThen]
              exact isStronglyNormalizing_of_noStep thenBranchHasNoStep
          | inr restBranch =>
              cases restBranch with
              | inl iotaFalseBranch =>
                  obtain ⟨_scrutineeIsFalse, targetIsElse⟩ := iotaFalseBranch
                  rw [targetIsElse]
                  exact isStronglyNormalizing_of_noStep elseBranchHasNoStep
              | inr congruenceBranch =>
                  cases congruenceBranch with
                  | inl scrutineeCongruence =>
                      obtain ⟨scrutineeAfter, targetIsScrutineeStep,
                        scrutineeStep⟩ := scrutineeCongruence
                      rw [targetIsScrutineeStep]
                      exact scrutineeIH scrutineeAfter scrutineeStep
                  | inr branchCongruence =>
                      cases branchCongruence with
                      | inl thenCongruence =>
                          obtain ⟨thenAfter, _targetIsThenStep, thenStep⟩ :=
                            thenCongruence
                          exact False.elim
                            (thenBranchHasNoStep thenAfter thenStep)
                      | inr elseCongruence =>
                          obtain ⟨elseAfter, _targetIsElseStep, elseStep⟩ :=
                            elseCongruence
                          exact False.elim
                            (elseBranchHasNoStep elseAfter elseStep)))
    scrutineeTerminates

end StepStar
end FX1Poly.Core
