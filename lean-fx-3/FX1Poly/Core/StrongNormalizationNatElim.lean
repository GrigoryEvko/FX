import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationIotaRedexes

/-! # FX1Poly/Core/StrongNormalizationNatElim
    — the recursive-eliminator iota-redex SN: natElim successor case (toward SN-061)

`StrongNormalizationIotaRedexes.lean` ships the iota-redex SN closures for the NON-recursive eliminators
whose ι-contractum is a passive branch (`boolElim`, `idJ`, `idStrictRec`).  `natElim` is the first RECURSIVE
eliminator: its successor ι-rule

```
natElim (natSucc pred) zeroBranch succBranch
  ↝ app (app succBranch pred) (natElim pred zeroBranch succBranch)
```

contracts to a two-level application whose right argument is the RECURSIVE CALL `natElim pred …`.  So unlike
`boolElim`, the contractum is not a passive branch — it is a fresh redex containing a structurally smaller
`natElim`.  This file ships:

* `predecessor_isStronglyNormalizing_of_natSucc` — the one-child subterm-SN lemma (the predecessor of a
  strongly-normalizing `natSucc` is strongly normalizing), completing the subterm-SN coverage alongside the
  two-child `firstComponent_of_pair` / `appHead_of_app` / `domain_of_piTyCode` (`StrongNormalizationSubterm`).
* `natElim_isStronglyNormalizing_of_normal_branches` — the conditional successor-case iota-redex SN: with both
  branches normal and the successor contractum strongly normalizing for every strongly-normalizing
  predecessor, a `natElim` redex with a strongly-normalizing scrutinee is strongly normalizing.

The `succContractumTerminates` hypothesis is the honest IH-carrying premise — it asserts the contractum (which
contains the recursive `natElim pred …` call) is SN for every SN predecessor.  This is exactly the obligation
the eventual well-founded recursion on the numeral structure discharges; here it is taken as a parameter, in
the same spirit as `appLam_isStronglyNormalizing_of_body_argument_contractum` parameterizes over the β
contractum.  This is the redex-SN building block toward SN-061 (natElim/natRec reducibility); the
numeral-WF-recursion tie-up that discharges the hypothesis is the remaining SN-061 content.

## Zero-axiom verification

The subterm lemma is `Acc` well-founded recursion generalized over the `natSucc` term (each predecessor step
lifts to a `natSucc` step via `StepChildren.here`), mirroring `firstComponent_isStronglyNormalizing_of_pair`.
The redex SN is `Acc.ndrec` on the scrutinee; `Step.from_natElim` splits the five arms — ι-zero lands on the
normal `zeroBranch`, ι-succ on the contractum (discharged by `succContractumTerminates` at the
subterm-SN predecessor), scrutinee-congruence by the induction hypothesis, and the two branch-congruences are
impossible (the branches are normal).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- **The predecessor of a strongly-normalizing `natSucc` is strongly normalizing.**  The one-child subterm-SN
lemma: each predecessor step lifts to a `natSucc` step (head congruence `StepChildren.here`), so accessibility
of `natSucc pred` descends to `pred`.  The `Acc` induction is generalized over the `natSucc` term so the
recursion's index is a variable, exactly as in `firstComponent_isStronglyNormalizing_of_pair`. -/
theorem predecessor_isStronglyNormalizing_of_natSucc {scope : Nat}
    {predecessor : RawTerm scope}
    (succTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil) : RawTerm scope)) :
    IsStronglyNormalizing predecessor := by
  suffices general :
      ∀ {succTerm : RawTerm scope}, Acc StepSuccessor succTerm →
        ∀ {currentPred : RawTerm scope},
          succTerm = .mkGen .gen_natSucc () (.childCons currentPred .childNil) →
          Acc StepSuccessor currentPred from
    general succTerminates rfl
  intro succTerm succAccessible
  induction succAccessible with
  | intro succWitness _succPredecessors succInductiveHypothesis =>
      intro currentPred witnessEq
      subst witnessEq
      apply Acc.intro
      intro predAfter predStep
      have congruenceLift :
          Step
            (.mkGen .gen_natSucc () (.childCons currentPred .childNil) : RawTerm scope)
            (.mkGen .gen_natSucc () (.childCons predAfter .childNil) : RawTerm scope) :=
        Step.cong .gen_natSucc () (StepChildren.here .childNil predStep)
      exact succInductiveHypothesis
        (.mkGen .gen_natSucc () (.childCons predAfter .childNil))
        congruenceLift rfl

/-- **The natElim successor-case iota-redex is strongly normalizing.**  With both branches normal and the
successor contractum strongly normalizing for every strongly-normalizing predecessor, a `natElim` redex with a
strongly-normalizing scrutinee is strongly normalizing.  `Acc.ndrec` runs on the scrutinee; `Step.from_natElim`
gives the five arms: ι-zero → the normal `zeroBranch`; ι-succ → the contractum, discharged by
`succContractumTerminates` at the predecessor (whose SN comes from the subterm lemma applied to the accessible
`natSucc` scrutinee); scrutinee-congruence → the induction hypothesis; branch-congruences → impossible by
branch normality.  The first recursive-eliminator iota-redex SN (toward SN-061). -/
theorem natElim_isStronglyNormalizing_of_normal_branches {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    (zeroBranchHasNoStep : ∀ targetZero : RawTerm scope, Step zeroBranch targetZero → False)
    (succBranchHasNoStep : ∀ targetSucc : RawTerm scope, Step succBranch targetSucc → False)
    (succContractumTerminates :
      ∀ {predecessor : RawTerm scope}, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons
                (.mkGen .gen_natElim ()
                  (.childCons predecessor
                    (.childCons zeroBranch (.childCons succBranch .childNil))))
                .childNil)) : RawTerm scope))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_natElim ()
        (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_natElim ()
          (.childCons currentScrutinee
            (.childCons zeroBranch (.childCons succBranch .childNil))) :
          RawTerm scope))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_natElim ()
          (.childCons currentScrutinee
            (.childCons zeroBranch (.childCons succBranch .childNil))) :
          RawTerm scope)
        (fun targetTerm natElimStep => by
          rcases Step.from_natElim natElimStep with
            ⟨_scrutineeIsZero, targetIsZero⟩ |
            ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
            ⟨zeroAfter, _targetIsZeroStep, zeroStep⟩ |
            ⟨succAfter, _targetIsSuccStep, succStep⟩
          · rw [targetIsZero]
            exact isStronglyNormalizing_of_noStep zeroBranchHasNoStep
          · rw [targetIsContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsSucc] at currentScrutineeSN
            exact succContractumTerminates
              (predecessor_isStronglyNormalizing_of_natSucc currentScrutineeSN)
          · rw [targetIsScrutineeStep]
            exact scrutineeIH scrutineeAfter scrutineeStep
          · exact absurd zeroStep (zeroBranchHasNoStep zeroAfter)
          · exact absurd succStep (succBranchHasNoStep succAfter)))
    scrutineeTerminates

/-- **The natRec successor-case iota-redex is strongly normalizing** — the dependent-recursor twin of
`natElim_isStronglyNormalizing_of_normal_branches`.  `gen_natRec` (the dependent recursor) shares
`gen_natElim`'s substrate metadata and its successor ι-rule shape (`Step.from_natRec` is the `gen_natRec`
mirror of `Step.from_natElim`), so the firing-case argument is identical: `Acc.ndrec` on the scrutinee, with
ι-succ discharged by `succContractumTerminates` at the `natSucc` predecessor subterm.  This is the normal-branch
firing-case complement of the shipped neutral-branch `natRecSucc_isStronglyNormalizing_of_neutral_succBranch`,
completing the firing-case formulation for the Nat recursor pair (toward SN-061). -/
theorem natRec_isStronglyNormalizing_of_normal_branches {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    (zeroBranchHasNoStep : ∀ targetZero : RawTerm scope, Step zeroBranch targetZero → False)
    (succBranchHasNoStep : ∀ targetSucc : RawTerm scope, Step succBranch targetSucc → False)
    (succContractumTerminates :
      ∀ {predecessor : RawTerm scope}, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons
                (.mkGen .gen_natRec ()
                  (.childCons predecessor
                    (.childCons zeroBranch (.childCons succBranch .childNil))))
                .childNil)) : RawTerm scope))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_natRec ()
        (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_natRec ()
          (.childCons currentScrutinee
            (.childCons zeroBranch (.childCons succBranch .childNil))) :
          RawTerm scope))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_natRec ()
          (.childCons currentScrutinee
            (.childCons zeroBranch (.childCons succBranch .childNil))) :
          RawTerm scope)
        (fun targetTerm natRecStep => by
          rcases Step.from_natRec natRecStep with
            ⟨_scrutineeIsZero, targetIsZero⟩ |
            ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
            ⟨zeroAfter, _targetIsZeroStep, zeroStep⟩ |
            ⟨succAfter, _targetIsSuccStep, succStep⟩
          · rw [targetIsZero]
            exact isStronglyNormalizing_of_noStep zeroBranchHasNoStep
          · rw [targetIsContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsSucc] at currentScrutineeSN
            exact succContractumTerminates
              (predecessor_isStronglyNormalizing_of_natSucc currentScrutineeSN)
          · rw [targetIsScrutineeStep]
            exact scrutineeIH scrutineeAfter scrutineeStep
          · exact absurd zeroStep (zeroBranchHasNoStep zeroAfter)
          · exact absurd succStep (succBranchHasNoStep succAfter)))
    scrutineeTerminates

/-- The natElim succ-contractum `app (app succBranch predecessor) (natElim predecessor zeroBranch succBranch)`. -/
private abbrev natElimSuccContractum {scope : Nat} (succBranch predecessor zeroBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
      (.childCons
        (.mkGen .gen_natElim ()
          (.childCons predecessor (.childCons zeroBranch (.childCons succBranch .childNil))))
        .childNil))

/-- **The natElim redex is strongly normalizing from SN (not necessarily normal) branches.**  The SN-branch
strengthening of `natElim_isStronglyNormalizing_of_normal_branches`, required for recursor REDUCIBILITY (SN-061):
in the Tait/data-candidate argument the branches are MEMBERS (hence SN) but not normal.  A triple nested
accessibility induction on `(scrutinee, zeroBranch, succBranch)`; the succ-contractum SN hypothesis is THREADED
through both branch inductions.  Under `zeroBranch`-congruence the update is one hop (the zero branch occurs once
in the contractum, inside the recursive `natElim`); under `succBranch`-congruence it is TWO hops (the succ branch
occurs TWICE — in `app succBranch predecessor` and in the recursive `natElim`), each discharged by app/natElim
congruence + `IsStronglyNormalizing.inv`.  This is the recursive analogue of the matcher SN-from-SN-branches:
the succ ι-contractum genuinely contains a recursive `natElim` call. -/
theorem natElim_isStronglyNormalizing_of_strongly_normalizing_branches {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    (succContractumTerminates :
      ∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natElimSuccContractum succBranch predecessor zeroBranch))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_natElim ()
        (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentZero currentSucc : RawTerm scope},
        IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
          (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
            IsStronglyNormalizing (natElimSuccContractum currentSucc predecessor currentZero)) →
          IsStronglyNormalizing
            (.mkGen .gen_natElim ()
              (.childCons currentScrutinee
                (.childCons currentZero (.childCons currentSucc .childNil)))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentZero currentSucc currentZeroTerminates currentSuccTerminates currentSuccContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerZero =>
            ∀ {currentSucc : RawTerm scope},
              IsStronglyNormalizing currentSucc →
                (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
                  IsStronglyNormalizing (natElimSuccContractum currentSucc predecessor innerZero)) →
                IsStronglyNormalizing
                  (.mkGen .gen_natElim ()
                    (.childCons currentScrutinee
                      (.childCons innerZero (.childCons currentSucc .childNil)))))
          (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
            intro currentSucc currentSuccTerminates currentInnerZeroContractum
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSucc =>
                  (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
                    IsStronglyNormalizing (natElimSuccContractum innerSucc predecessor currentInnerZero)) →
                    IsStronglyNormalizing
                      (.mkGen .gen_natElim ()
                        (.childCons currentScrutinee
                          (.childCons currentInnerZero (.childCons innerSucc .childNil)))))
                (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
                      intro currentInnerSuccContractum
                      apply Acc.intro
                      intro targetTerm natElimStep
                      rcases Step.from_natElim natElimStep with
                        ⟨_scrutineeIsZero, targetIsZero⟩ |
                        ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                        ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
                        ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                        ⟨succAfter, targetIsSuccStep, succStep⟩
                      · rw [targetIsZero]
                        exact Acc.intro currentInnerZero currentInnerZeroSuccessors
                      · rw [targetIsContractum]
                        have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                          Acc.intro currentScrutinee currentScrutineeSuccessors
                        rw [scrutineeIsSucc] at currentScrutineeSN
                        exact currentInnerSuccContractum predecessor
                          (predecessor_isStronglyNormalizing_of_natSucc currentScrutineeSN)
                      · rw [targetIsScrutineeStep]
                        exact scrutineeIH scrutineeAfter scrutineeStep
                          (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                          (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                          currentInnerSuccContractum
                      · rw [targetIsZeroStep]
                        refine zeroIH zeroAfter zeroStep
                          (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                          (fun predecessor predecessorTerminates => ?_)
                        exact (currentInnerSuccContractum predecessor predecessorTerminates).inv
                          (Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons currentInnerSucc (.childCons predecessor .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_natElim ()
                                  (StepChildren.there (headShift := 0) predecessor
                                    (StepChildren.here
                                      (.childCons currentInnerSucc .childNil : RawTermChildren [0] scope)
                                      zeroStep))))))
                      · rw [targetIsSuccStep]
                        refine succIH succAfter succStep (fun predecessor predecessorTerminates => ?_)
                        have hopOne :
                            Step (natElimSuccContractum currentInnerSucc predecessor currentInnerZero)
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons succAfter (.childCons predecessor .childNil)))
                                  (.childCons
                                    (.mkGen .gen_natElim ()
                                      (.childCons predecessor
                                        (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                    .childNil))) :=
                          Step.cong .gen_app ()
                            (StepChildren.here
                              (.childCons
                                (.mkGen .gen_natElim ()
                                  (.childCons predecessor
                                    (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                .childNil : RawTermChildren [0] scope)
                              (Step.cong .gen_app ()
                                (StepChildren.here
                                  (.childCons predecessor .childNil : RawTermChildren [0] scope) succStep)))
                        have hopTwo :
                            Step
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons succAfter (.childCons predecessor .childNil)))
                                  (.childCons
                                    (.mkGen .gen_natElim ()
                                      (.childCons predecessor
                                        (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                    .childNil)))
                              (natElimSuccContractum succAfter predecessor currentInnerZero) :=
                          Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons succAfter (.childCons predecessor .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_natElim ()
                                  (StepChildren.there (headShift := 0) predecessor
                                    (StepChildren.there (headShift := 0) currentInnerZero
                                      (StepChildren.here .childNil succStep))))))
                        exact (((currentInnerSuccContractum predecessor predecessorTerminates).inv hopOne).inv
                          hopTwo))
                currentSuccTerminates currentInnerZeroContractum)
          currentZeroTerminates currentSuccTerminates currentSuccContractum))
    scrutineeTerminates)
    zeroBranchTerminates succBranchTerminates succContractumTerminates

/-- The natRec succ-contractum `app (app succBranch predecessor) (natRec predecessor zeroBranch succBranch)`. -/
private abbrev natRecSuccContractum {scope : Nat} (succBranch predecessor zeroBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
      (.childCons
        (.mkGen .gen_natRec ()
          (.childCons predecessor (.childCons zeroBranch (.childCons succBranch .childNil))))
        .childNil))

/-- **The natRec redex is strongly normalizing from SN (not necessarily normal) branches** — the dependent-recursor
twin of `natElim_isStronglyNormalizing_of_strongly_normalizing_branches`, identical structure with the recursive
`natRec` call in the succ contractum. -/
theorem natRec_isStronglyNormalizing_of_strongly_normalizing_branches {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    (succContractumTerminates :
      ∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natRecSuccContractum succBranch predecessor zeroBranch))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_natRec ()
        (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentZero currentSucc : RawTerm scope},
        IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
          (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
            IsStronglyNormalizing (natRecSuccContractum currentSucc predecessor currentZero)) →
          IsStronglyNormalizing
            (.mkGen .gen_natRec ()
              (.childCons currentScrutinee
                (.childCons currentZero (.childCons currentSucc .childNil)))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentZero currentSucc currentZeroTerminates currentSuccTerminates currentSuccContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerZero =>
            ∀ {currentSucc : RawTerm scope},
              IsStronglyNormalizing currentSucc →
                (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
                  IsStronglyNormalizing (natRecSuccContractum currentSucc predecessor innerZero)) →
                IsStronglyNormalizing
                  (.mkGen .gen_natRec ()
                    (.childCons currentScrutinee
                      (.childCons innerZero (.childCons currentSucc .childNil)))))
          (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
            intro currentSucc currentSuccTerminates currentInnerZeroContractum
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSucc =>
                  (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
                    IsStronglyNormalizing (natRecSuccContractum innerSucc predecessor currentInnerZero)) →
                    IsStronglyNormalizing
                      (.mkGen .gen_natRec ()
                        (.childCons currentScrutinee
                          (.childCons currentInnerZero (.childCons innerSucc .childNil)))))
                (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
                      intro currentInnerSuccContractum
                      apply Acc.intro
                      intro targetTerm natRecStep
                      rcases Step.from_natRec natRecStep with
                        ⟨_scrutineeIsZero, targetIsZero⟩ |
                        ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                        ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
                        ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                        ⟨succAfter, targetIsSuccStep, succStep⟩
                      · rw [targetIsZero]
                        exact Acc.intro currentInnerZero currentInnerZeroSuccessors
                      · rw [targetIsContractum]
                        have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                          Acc.intro currentScrutinee currentScrutineeSuccessors
                        rw [scrutineeIsSucc] at currentScrutineeSN
                        exact currentInnerSuccContractum predecessor
                          (predecessor_isStronglyNormalizing_of_natSucc currentScrutineeSN)
                      · rw [targetIsScrutineeStep]
                        exact scrutineeIH scrutineeAfter scrutineeStep
                          (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                          (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                          currentInnerSuccContractum
                      · rw [targetIsZeroStep]
                        refine zeroIH zeroAfter zeroStep
                          (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                          (fun predecessor predecessorTerminates => ?_)
                        exact (currentInnerSuccContractum predecessor predecessorTerminates).inv
                          (Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons currentInnerSucc (.childCons predecessor .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_natRec ()
                                  (StepChildren.there (headShift := 0) predecessor
                                    (StepChildren.here
                                      (.childCons currentInnerSucc .childNil : RawTermChildren [0] scope)
                                      zeroStep))))))
                      · rw [targetIsSuccStep]
                        refine succIH succAfter succStep (fun predecessor predecessorTerminates => ?_)
                        have hopOne :
                            Step (natRecSuccContractum currentInnerSucc predecessor currentInnerZero)
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons succAfter (.childCons predecessor .childNil)))
                                  (.childCons
                                    (.mkGen .gen_natRec ()
                                      (.childCons predecessor
                                        (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                    .childNil))) :=
                          Step.cong .gen_app ()
                            (StepChildren.here
                              (.childCons
                                (.mkGen .gen_natRec ()
                                  (.childCons predecessor
                                    (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                .childNil : RawTermChildren [0] scope)
                              (Step.cong .gen_app ()
                                (StepChildren.here
                                  (.childCons predecessor .childNil : RawTermChildren [0] scope) succStep)))
                        have hopTwo :
                            Step
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons succAfter (.childCons predecessor .childNil)))
                                  (.childCons
                                    (.mkGen .gen_natRec ()
                                      (.childCons predecessor
                                        (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                    .childNil)))
                              (natRecSuccContractum succAfter predecessor currentInnerZero) :=
                          Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons succAfter (.childCons predecessor .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_natRec ()
                                  (StepChildren.there (headShift := 0) predecessor
                                    (StepChildren.there (headShift := 0) currentInnerZero
                                      (StepChildren.here .childNil succStep))))))
                        exact (((currentInnerSuccContractum predecessor predecessorTerminates).inv hopOne).inv
                          hopTwo))
                currentSuccTerminates currentInnerZeroContractum)
          currentZeroTerminates currentSuccTerminates currentSuccContractum))
    scrutineeTerminates)
    zeroBranchTerminates succBranchTerminates succContractumTerminates

end StepStar
end FX1Poly.Core
