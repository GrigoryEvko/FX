import FX1Poly.Core.StrongNormalizationIotaRedexes

/-! # Foundation/PolyCell/Core/BoolElimStrongNormalization
    — `boolElim` is strongly normalizing when its scrutinee AND both branches are SN (the eliminator frontier)

`StrongNormalizationIotaRedexes.lean` proves `boolElim_isStronglyNormalizing_of_normal_branches`: the
`boolElim` redex is SN when the motive and branches are already NORMAL.  That suffices for the SN proof of
the raw substrate but is too weak for **eliminator reducibility**: in the Tait argument the branches are
MEMBERS of the motive's reducibility candidate, hence strongly normalizing but not necessarily normal.  This
file strengthens the result to SN components: `boolElim motive thenBranch elseBranch scrutinee` (Phase-Z
motive shape: motive first under one binder, scrutinee last) is strongly normalizing whenever all four
components are.

This is the iota-head-expansion SN foundation for `boolElim` reducibility (toward the fundamental
theorem's `boolElim` arm): a `boolElim`-headed redex whose contractum (the selected branch) is reducible — and
whose other components are SN — is itself SN, the prerequisite for showing the redex inherits candidate
membership.

## Proof shape

A four-fold nested accessibility induction on `(scrutinee, motive, thenBranch, elseBranch)` — the
generalization of `isStronglyNormalizing_of_twoChildCong`, extended to absorb the `boolElim` ι-redex and the
new motive child (under one binder, at `scope + 1`).  At the innermost point the `Step.from_boolElim`
inversion splits six ways:

* **ι-true / ι-false** — the target IS the current (then / else) branch, strongly normalizing directly from
  that branch's own accessibility witness (`Acc.intro` reconstructs it from the inner successors).
* **motive / then / else / scrutinee congruence** — the target is a `boolElim` with one component stepped,
  handled by the matching induction hypothesis, fed the unchanged components' SN witnesses.

No component need be normal: every congruence reduct is discharged by that component's own
accessibility induction.

## Zero-axiom verification

`Acc.ndrec` (four nested), `Step.from_boolElim` (cased Step ctors, no propext), `Acc.intro`, and `rw` on the
target equalities.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- **`boolElim` is strongly normalizing when its motive, scrutinee, and both branches are.**  The
SN-component strengthening of `boolElim_isStronglyNormalizing_of_normal_branches`, by four-fold accessibility
induction (scrutinee outer, motive at `scope + 1`, then-branch, else-branch innermost) with the ι-redex
absorbed into the innermost step inversion (the ι-fire lands on the current branch, SN by its own
accessibility; congruences recurse on the matching induction hypothesis).  Phase-Z motive shape: the children
spine is `(motive, thenBranch, elseBranch, scrutinee)`. -/
theorem boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
    {scope : Nat} {motive : RawTerm (scope + 1)}
    {scrutinee thenBranch elseBranch : RawTerm scope}
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (thenBranchTerminates : IsStronglyNormalizing thenBranch)
    (elseBranchTerminates : IsStronglyNormalizing elseBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_boolElim ()
        (.childCons motive
          (.childCons thenBranch
            (.childCons elseBranch (.childCons scrutinee .childNil)))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentMotive : RawTerm (scope + 1)} {currentThen currentElse : RawTerm scope},
        IsStronglyNormalizing currentMotive →
        IsStronglyNormalizing currentThen → IsStronglyNormalizing currentElse →
          IsStronglyNormalizing
            (.mkGen .gen_boolElim ()
              (.childCons currentMotive
                (.childCons currentThen
                  (.childCons currentElse (.childCons currentScrutinee .childNil))))))
    (m := fun currentScrutinee _currentScrutineeSuccessors scrutineeIH => by
      intro currentMotive currentThen currentElse
        currentMotiveTerminates currentThenTerminates currentElseTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            ∀ {innerThen innerElse : RawTerm scope},
              IsStronglyNormalizing innerThen → IsStronglyNormalizing innerElse →
                IsStronglyNormalizing
                  (.mkGen .gen_boolElim ()
                    (.childCons innerMotive
                      (.childCons innerThen
                        (.childCons innerElse (.childCons currentScrutinee .childNil))))))
          (m := fun currentInnerMotive currentInnerMotiveSuccessors motiveIH => by
            intro innerThen innerElse innerThenTerminates innerElseTerminates
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerThen' =>
                  ∀ {innerElse' : RawTerm scope},
                    IsStronglyNormalizing innerElse' →
                      IsStronglyNormalizing
                        (.mkGen .gen_boolElim ()
                          (.childCons currentInnerMotive
                            (.childCons innerThen'
                              (.childCons innerElse'
                                (.childCons currentScrutinee .childNil))))))
                (m := fun currentInnerThen currentInnerThenSuccessors thenIH => by
                  intro innerElse' innerElseTerminates'
                  exact
                    Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerElse'' =>
                        IsStronglyNormalizing
                          (.mkGen .gen_boolElim ()
                            (.childCons currentInnerMotive
                              (.childCons currentInnerThen
                                (.childCons innerElse''
                                  (.childCons currentScrutinee .childNil))))))
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
                                    | inl motiveCongruence =>
                                        obtain ⟨motiveAfter, targetEq, motiveStep⟩ :=
                                          motiveCongruence
                                        rw [targetEq]
                                        exact motiveIH motiveAfter motiveStep
                                          (Acc.intro currentInnerThen currentInnerThenSuccessors)
                                          (Acc.intro currentInnerElse currentInnerElseSuccessors)
                                    | inr restAfterMotive =>
                                        cases restAfterMotive with
                                        | inl thenCongruence =>
                                            obtain ⟨thenAfter, targetEq, thenStep⟩ := thenCongruence
                                            rw [targetEq]
                                            exact thenIH thenAfter thenStep
                                              (Acc.intro currentInnerElse currentInnerElseSuccessors)
                                        | inr restAfterThen =>
                                            cases restAfterThen with
                                            | inl elseCongruence =>
                                                obtain ⟨elseAfter, targetEq, elseStep⟩ :=
                                                  elseCongruence
                                                rw [targetEq]
                                                exact elseIH elseAfter elseStep
                                            | inr scrutineeCongruence =>
                                                obtain ⟨scrutineeAfter, targetEq, scrutineeStep⟩ :=
                                                  scrutineeCongruence
                                                rw [targetEq]
                                                exact scrutineeIH scrutineeAfter scrutineeStep
                                                  (Acc.intro currentInnerMotive
                                                    currentInnerMotiveSuccessors)
                                                  (Acc.intro currentInnerThen
                                                    currentInnerThenSuccessors)
                                                  (Acc.intro currentInnerElse
                                                    currentInnerElseSuccessors))
                      innerElseTerminates')
                innerThenTerminates) innerElseTerminates)
          currentMotiveTerminates) currentThenTerminates currentElseTerminates)
    scrutineeTerminates)
    motiveTerminates thenBranchTerminates elseBranchTerminates

end StepStar
end FX1Poly.Core
