import FX1Poly.Core.StrongNormalizationIotaRedexes

/-! # Foundation/PolyCell/Core/BoolElimStrongNormalization
    — `boolElim` is strongly normalizing when its scrutinee AND both branches are SN (the eliminator frontier)

`StrongNormalizationIotaRedexes.lean` proves `boolElim_isStronglyNormalizing_of_normal_branches`: the
`boolElim` redex is SN when the branches are already NORMAL.  That suffices for the SN proof of the raw
substrate but is too weak for **eliminator reducibility**: in the Tait argument the branches are MEMBERS of
the motive's reducibility candidate, hence strongly normalizing but not necessarily normal.  This file
strengthens the result to SN branches: `boolElim scrutinee thenBranch elseBranch` is strongly normalizing
whenever all three components are.

This is the iota-head-expansion SN foundation for `boolElim` reducibility (toward the fundamental
theorem's `boolElim` arm): a `boolElim`-headed redex whose contractum (the selected branch) is reducible — and
whose other components are SN — is itself SN, the prerequisite for showing the redex inherits candidate
membership.

## Proof shape

A triple nested accessibility induction on `(scrutinee, thenBranch, elseBranch)` — the three-argument
generalization of `isStronglyNormalizing_of_twoChildCong`, extended to absorb the `boolElim` ι-redex.  At the
innermost point the `Step.from_boolElim` inversion splits five ways:

* **ι-true / ι-false** — the target IS the current (then / else) branch, strongly normalizing directly from
  that branch's own accessibility witness (`Acc.intro` reconstructs it from the inner successors).
* **scrutinee / then / else congruence** — the target is a `boolElim` with one component stepped, handled by
  the outer / middle / inner induction hypothesis respectively, fed the unchanged components' SN witnesses.

The branches need not be normal: their congruence reducts are discharged by their own
accessibility inductions.

## Zero-axiom verification

`Acc.ndrec` (three nested), `Step.from_boolElim` (cased Step ctors, no propext), `Acc.intro`, and `rw` on the
target equalities.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- **`boolElim` is strongly normalizing when its scrutinee and both branches are.**  The SN-branch
strengthening of `boolElim_isStronglyNormalizing_of_normal_branches`, by triple accessibility induction with
the ι-redex absorbed into the innermost step inversion (the ι-fire lands on the current branch, SN by its own
accessibility; congruences recurse on the matching induction hypothesis). -/
theorem boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
    {scope : Nat} {scrutinee thenBranch elseBranch : RawTerm scope}
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (thenBranchTerminates : IsStronglyNormalizing thenBranch)
    (elseBranchTerminates : IsStronglyNormalizing elseBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_boolElim ()
        (.childCons scrutinee
          (.childCons thenBranch (.childCons elseBranch .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentThen currentElse : RawTerm scope},
        IsStronglyNormalizing currentThen → IsStronglyNormalizing currentElse →
          IsStronglyNormalizing
            (.mkGen .gen_boolElim ()
              (.childCons currentScrutinee
                (.childCons currentThen (.childCons currentElse .childNil)))))
    (m := fun currentScrutinee _currentScrutineeSuccessors scrutineeIH => by
      intro currentThen currentElse currentThenTerminates currentElseTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerThen =>
            ∀ {innerElse : RawTerm scope},
              IsStronglyNormalizing innerElse →
                IsStronglyNormalizing
                  (.mkGen .gen_boolElim ()
                    (.childCons currentScrutinee
                      (.childCons innerThen (.childCons innerElse .childNil)))))
          (m := fun currentInnerThen currentInnerThenSuccessors thenIH => by
            intro innerElse innerElseTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerElse' =>
                  IsStronglyNormalizing
                    (.mkGen .gen_boolElim ()
                      (.childCons currentScrutinee
                        (.childCons currentInnerThen (.childCons innerElse' .childNil)))))
                (m := fun currentInnerElse currentInnerElseSuccessors elseIH => by
                      apply Acc.intro
                      intro targetTerm boolElimStep
                      cases Step.from_boolElim boolElimStep with
                      | inl iotaTrue =>
                          obtain ⟨_scrutineeIsTrue, targetIsThen⟩ := iotaTrue
                          rw [targetIsThen]
                          exact Acc.intro currentInnerThen currentInnerThenSuccessors
                      | inr restAfterTrue =>
                          cases restAfterTrue with
                          | inl iotaFalse =>
                              obtain ⟨_scrutineeIsFalse, targetIsElse⟩ := iotaFalse
                              rw [targetIsElse]
                              exact Acc.intro currentInnerElse currentInnerElseSuccessors
                          | inr restAfterFalse =>
                              cases restAfterFalse with
                              | inl scrutineeCongruence =>
                                  obtain ⟨scrutineeAfter, targetEq, scrutineeStep⟩ :=
                                    scrutineeCongruence
                                  rw [targetEq]
                                  exact scrutineeIH scrutineeAfter scrutineeStep
                                    (Acc.intro currentInnerThen currentInnerThenSuccessors)
                                    (Acc.intro currentInnerElse currentInnerElseSuccessors)
                              | inr branchCongruence =>
                                  cases branchCongruence with
                                  | inl thenCongruence =>
                                      obtain ⟨thenAfter, targetEq, thenStep⟩ := thenCongruence
                                      rw [targetEq]
                                      exact thenIH thenAfter thenStep
                                        (Acc.intro currentInnerElse currentInnerElseSuccessors)
                                  | inr elseCongruence =>
                                      obtain ⟨elseAfter, targetEq, elseStep⟩ := elseCongruence
                                      rw [targetEq]
                                      exact elseIH elseAfter elseStep)
                innerElseTerminates)
          currentThenTerminates)
        currentElseTerminates)
    scrutineeTerminates)
    thenBranchTerminates elseBranchTerminates

end StepStar
end FX1Poly.Core
