import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationIotaRedexes

/-! # FX1Poly/Core/StrongNormalizationNatElim
    — the recursive-eliminator iota-redex SN: natElim successor case

`StrongNormalizationIotaRedexes.lean` ships the iota-redex SN closures for the NON-recursive eliminators
whose ι-contractum is a passive branch (`boolElim`, `idJ`, `idStrictRec`).  `natElim` is the first RECURSIVE
eliminator.  Phase-Z motive shape (arity 4, `binderShifts [1, 0, 2, 0]`, spine
`(motive, zeroBranch, succBranch, scrutinee)` with the scrutinee LAST), the successor ι-rule SUBSTITUTES:

```
natElim motive zeroBranch succBranch (natSucc pred)
  ↝ succBranch[var 0 := natElim motive zeroBranch succBranch pred, var 1 := pred]
```

where the succ-branch is a `RawTerm (scope + 2)` (`var 0` = inductive hypothesis = recursive call, `var 1` =
predecessor), so the reduct is the simultaneous substitution
`subst (cons recursiveCall (singleton pred)) succBranch`.  Unlike the `listElim` cons-iota (a pure app-chain
reassembly whose SN follows by congruence), this SUBSTITUTING reduct's SN does NOT follow from
`SN succBranch + SN pred + SN recursiveCall` by congruence (substitution can duplicate the recursive call or
place subterms under fresh redex contexts — exactly β's situation, which is why raw SN is FALSE globally).
This file ships:

* `predecessor_isStronglyNormalizing_of_natSucc` — the one-child subterm-SN lemma (the predecessor of a
  strongly-normalizing `natSucc` is strongly normalizing), completing the subterm-SN coverage alongside the
  two-child `firstComponent_of_pair` / `appHead_of_app` / `domain_of_piTyCode` (`StrongNormalizationSubterm`).
* `natElim_isStronglyNormalizing_of_normal_branches` — the conditional successor-case iota-redex SN: with the
  motive and both branches normal and the SUBSTITUTED successor contractum strongly normalizing for every
  strongly-normalizing predecessor, a `natElim` redex with a strongly-normalizing scrutinee is strongly
  normalizing.

The `succContractumTerminates` hypothesis is the honest IH-carrying premise — it asserts the SUBSTITUTED
contractum (which contains the recursive `natElim … pred` call) is SN for every SN predecessor.  Because the
reduct is a substitution (not an app-chain), the branch-congruence cases re-derive this premise at the stepped
branch from the SAME universally-quantified hypothesis rather than via `.inv` congruence hops — the
substitution analogue of the β-redex SN helper `appLam_isStronglyNormalizing_of_normal_body_contractum`, which
likewise parameterizes over the β contractum.  This is the redex-SN building block toward natElim/natRec
reducibility; the numeral-WF-recursion tie-up that discharges the hypothesis is the remaining content.

## Zero-axiom verification

The subterm lemma is `Acc` well-founded recursion generalized over the `natSucc` term (each predecessor step
lifts to a `natSucc` step via `StepChildren.here`), mirroring `firstComponent_isStronglyNormalizing_of_pair`.
The redex SN is `Acc.ndrec` on the scrutinee; the PINNED 6-way `Step.from_natElim` splits the arms — ι-zero
lands on the normal `zeroBranch`, ι-succ on the SUBSTITUTED contractum (discharged by `succContractumTerminates`
at the subterm-SN predecessor), scrutinee-congruence (the LAST child) by the induction hypothesis, and the
motive + two branch-congruences are impossible (all normal).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
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

/-- The natElim succ-iota SUBSTITUTED reduct
`subst (cons (natElim motive zeroBranch succBranch predecessor) (singleton predecessor)) succBranch`.
Phase-Z motive shape (`binderShifts [1, 0, 2, 0]`): the succ-branch is a `RawTerm (scope + 2)` whose `var 0`
is the inductive hypothesis (the recursive call) and `var 1` is the predecessor; the succ-iota substitutes
BOTH simultaneously.  Unlike the `listElim` cons-contractum (a pure app-chain reassembly), this reduct is a
SUBSTITUTION — its SN does NOT follow by congruence from `SN succBranch + SN predecessor + SN recursiveCall`
(substitution can duplicate the recursive call or place it under fresh redex contexts — beta's situation,
which is why raw SN is FALSE globally).  So every SN helper below takes the SN of THIS reduct as an explicit
universally-quantified premise. -/
private abbrev natElimSuccContractum {scope : Nat} (motive : RawTerm (scope + 1))
    (succBranch : RawTerm (scope + 2)) (predecessor zeroBranch : RawTerm scope) :
    RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- **The natElim successor-case iota-redex is strongly normalizing.**  With the motive and both branches
normal and the SUBSTITUTED successor contractum strongly normalizing for every strongly-normalizing
predecessor, a `natElim` redex with a strongly-normalizing scrutinee is strongly normalizing.  `Acc.ndrec`
runs on the scrutinee; the PINNED 6-way `Step.from_natElim` gives the arms: ι-zero → the normal `zeroBranch`;
ι-succ → the SUBSTITUTED contractum, discharged by `succContractumTerminates` at the predecessor (whose SN
comes from the subterm lemma applied to the accessible `natSucc` scrutinee); scrutinee-congruence → the
induction hypothesis; motive/branch-congruences → impossible by normality.  Phase-Z motive shape: the children
spine is `(motive, zeroBranch, succBranch, scrutinee)` with the motive under one binder, the succ-branch under
two binders, and the scrutinee LAST.  The first recursive-eliminator iota-redex SN with a SUBSTITUTING reduct. -/
theorem natElim_isStronglyNormalizing_of_normal_branches {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (motiveHasNoStep : ∀ targetMotive : RawTerm (scope + 1), Step motive targetMotive → False)
    (zeroBranchHasNoStep : ∀ targetZero : RawTerm scope, Step zeroBranch targetZero → False)
    (succBranchHasNoStep : ∀ targetSucc : RawTerm (scope + 2), Step succBranch targetSucc → False)
    (succContractumTerminates :
      ∀ {predecessor : RawTerm scope}, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natElimSuccContractum motive succBranch predecessor zeroBranch))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch (.childCons scrutinee .childNil)))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch (.childCons currentScrutinee .childNil)))) :
          RawTerm scope))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch (.childCons currentScrutinee .childNil)))) :
          RawTerm scope)
        (fun targetTerm natElimStep => by
          rcases Step.from_natElim natElimStep with
            ⟨_scrutineeIsZero, targetIsZero⟩ |
            ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
            ⟨motiveAfter, _targetIsMotiveStep, motiveStep⟩ |
            ⟨zeroAfter, _targetIsZeroStep, zeroStep⟩ |
            ⟨succAfter, _targetIsSuccStep, succStep⟩ |
            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
          · rw [targetIsZero]
            exact isStronglyNormalizing_of_noStep zeroBranchHasNoStep
          · rw [targetIsContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsSucc] at currentScrutineeSN
            exact succContractumTerminates
              (predecessor_isStronglyNormalizing_of_natSucc currentScrutineeSN)
          · exact absurd motiveStep (motiveHasNoStep motiveAfter)
          · exact absurd zeroStep (zeroBranchHasNoStep zeroAfter)
          · exact absurd succStep (succBranchHasNoStep succAfter)
          · rw [targetIsScrutineeStep]
            exact scrutineeIH scrutineeAfter scrutineeStep))
    scrutineeTerminates

/-- The natRec succ-iota SUBSTITUTED reduct — the `gen_natRec` mirror of `natElimSuccContractum` (the
substrate treats the two recursors identically, so the substitution shape is the same with `gen_natRec`). -/
private abbrev natRecSuccContractum {scope : Nat} (motive : RawTerm (scope + 1))
    (succBranch : RawTerm (scope + 2)) (predecessor zeroBranch : RawTerm scope) :
    RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- **The natRec successor-case iota-redex is strongly normalizing** — the dependent-recursor twin of
`natElim_isStronglyNormalizing_of_normal_branches`.  `gen_natRec` shares `gen_natElim`'s substrate metadata and
its SUBSTITUTING successor ι-rule shape (`Step.from_natRec` is the `gen_natRec` mirror of `Step.from_natElim`),
so the firing-case argument is identical: `Acc.ndrec` on the scrutinee (LAST child), with ι-succ discharged by
`succContractumTerminates` at the `natSucc` predecessor subterm.  This is the normal-branch firing-case
complement of the substitution-form successor lemma `natRecSucc_isStronglyNormalizing_of_normal_branches`
(`StrongNormalizationRedexes`, which replaced the retired app-chain neutral-branch helper), completing the
firing-case formulation for the Nat recursor pair. -/
theorem natRec_isStronglyNormalizing_of_normal_branches {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (motiveHasNoStep : ∀ targetMotive : RawTerm (scope + 1), Step motive targetMotive → False)
    (zeroBranchHasNoStep : ∀ targetZero : RawTerm scope, Step zeroBranch targetZero → False)
    (succBranchHasNoStep : ∀ targetSucc : RawTerm (scope + 2), Step succBranch targetSucc → False)
    (succContractumTerminates :
      ∀ {predecessor : RawTerm scope}, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natRecSuccContractum motive succBranch predecessor zeroBranch))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch (.childCons scrutinee .childNil)))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch (.childCons currentScrutinee .childNil)))) :
          RawTerm scope))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch (.childCons currentScrutinee .childNil)))) :
          RawTerm scope)
        (fun targetTerm natRecStep => by
          rcases Step.from_natRec natRecStep with
            ⟨_scrutineeIsZero, targetIsZero⟩ |
            ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
            ⟨motiveAfter, _targetIsMotiveStep, motiveStep⟩ |
            ⟨zeroAfter, _targetIsZeroStep, zeroStep⟩ |
            ⟨succAfter, _targetIsSuccStep, succStep⟩ |
            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
          · rw [targetIsZero]
            exact isStronglyNormalizing_of_noStep zeroBranchHasNoStep
          · rw [targetIsContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsSucc] at currentScrutineeSN
            exact succContractumTerminates
              (predecessor_isStronglyNormalizing_of_natSucc currentScrutineeSN)
          · exact absurd motiveStep (motiveHasNoStep motiveAfter)
          · exact absurd zeroStep (zeroBranchHasNoStep zeroAfter)
          · exact absurd succStep (succBranchHasNoStep succAfter)
          · rw [targetIsScrutineeStep]
            exact scrutineeIH scrutineeAfter scrutineeStep))
    scrutineeTerminates

/-- **The natElim redex is strongly normalizing from SN (not necessarily normal) branches.**  The SN-branch
strengthening of `natElim_isStronglyNormalizing_of_normal_branches`, required for recursor REDUCIBILITY:
in the Tait/data-candidate argument the motive and branches are MEMBERS (hence SN) but not normal.  Phase-Z
motive shape: a FOUR-fold nested accessibility induction on `(scrutinee, motive, zeroBranch, succBranch)` with
the SUBSTITUTED succ-contractum SN hypothesis THREADED through the motive AND both branch inductions.

**The substitution headline (why this is NOT the listElim pattern):** the `listElim` cons-iota reduct is an
app-chain, so under a branch step its contractum relates to the stepped-branch contractum by an explicit
`.inv hopOne hopTwo` congruence walk.  The natElim succ-iota reduct is a SUBSTITUTION
`subst (cons recursiveCall (singleton pred)) succBranch` — there is NO Step relating `subst σ succBranch` to
`subst σ' succAfter` by congruence (substitution can duplicate/relocate `recursiveCall`).  So the
`succContractumTerminates` premise is universally quantified over the CURRENT (possibly-stepped)
motive/zeroBranch/succBranch/predecessor, and every congruence arm RE-INVOKES the IH passing the SAME universal
premise re-instantiated at the stepped motive/branch — no `.inv`.  Pinned premise order:
`(substitutedReductTerminates, scrutinee, motive, zero, succ)` terminate. -/
theorem natElim_isStronglyNormalizing_of_strongly_normalizing_branches {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (succContractumTerminates :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentSucc : RawTerm (scope + 2))
        (predecessor currentZero : RawTerm scope), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natElimSuccContractum currentMotive currentSucc predecessor currentZero))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch (.childCons scrutinee .childNil))))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentMotive : RawTerm (scope + 1)} {currentZero : RawTerm scope}
        {currentSucc : RawTerm (scope + 2)},
        IsStronglyNormalizing currentMotive →
        IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
          (∀ (innerMotive : RawTerm (scope + 1)) (innerSucc : RawTerm (scope + 2))
            (predecessor innerZero : RawTerm scope), IsStronglyNormalizing predecessor →
            IsStronglyNormalizing (natElimSuccContractum innerMotive innerSucc predecessor innerZero)) →
          IsStronglyNormalizing
            (.mkGen .gen_natElim ()
              (.childCons currentMotive
                (.childCons currentZero
                  (.childCons currentSucc (.childCons currentScrutinee .childNil))))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentMotive currentZero currentSucc
        currentMotiveTerminates currentZeroTerminates currentSuccTerminates currentContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            ∀ {currentZero : RawTerm scope} {currentSucc : RawTerm (scope + 2)},
              IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
                (∀ (innerMotive' : RawTerm (scope + 1)) (innerSucc : RawTerm (scope + 2))
                  (predecessor innerZero : RawTerm scope), IsStronglyNormalizing predecessor →
                  IsStronglyNormalizing (natElimSuccContractum innerMotive' innerSucc predecessor innerZero)) →
                IsStronglyNormalizing
                  (.mkGen .gen_natElim ()
                    (.childCons innerMotive
                      (.childCons currentZero
                        (.childCons currentSucc (.childCons currentScrutinee .childNil))))))
          (m := fun currentInnerMotive currentInnerMotiveSuccessors motiveIH => by
            intro currentZero currentSucc currentZeroTerminates currentSuccTerminates currentInnerMotiveContractum
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerZero =>
                  ∀ {currentSucc : RawTerm (scope + 2)},
                    IsStronglyNormalizing currentSucc →
                      (∀ (innerMotive' : RawTerm (scope + 1)) (innerSucc : RawTerm (scope + 2))
                        (predecessor innerZero' : RawTerm scope), IsStronglyNormalizing predecessor →
                        IsStronglyNormalizing
                          (natElimSuccContractum innerMotive' innerSucc predecessor innerZero')) →
                      IsStronglyNormalizing
                        (.mkGen .gen_natElim ()
                          (.childCons currentInnerMotive
                            (.childCons innerZero
                              (.childCons currentSucc (.childCons currentScrutinee .childNil))))))
                (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
                  intro currentSucc currentSuccTerminates currentInnerZeroContractum
                  exact
                    Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerSucc =>
                        (∀ (innerMotive' : RawTerm (scope + 1)) (innerSucc' : RawTerm (scope + 2))
                          (predecessor innerZero' : RawTerm scope), IsStronglyNormalizing predecessor →
                          IsStronglyNormalizing
                            (natElimSuccContractum innerMotive' innerSucc' predecessor innerZero')) →
                          IsStronglyNormalizing
                            (.mkGen .gen_natElim ()
                              (.childCons currentInnerMotive
                                (.childCons currentInnerZero
                                  (.childCons innerSucc (.childCons currentScrutinee .childNil))))))
                      (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
                            intro currentInnerSuccContractum
                            apply Acc.intro
                            intro targetTerm natElimStep
                            rcases Step.from_natElim natElimStep with
                              ⟨_scrutineeIsZero, targetIsZero⟩ |
                              ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                              ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                              ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                              ⟨succAfter, targetIsSuccStep, succStep⟩ |
                              ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                            · rw [targetIsZero]
                              exact Acc.intro currentInnerZero currentInnerZeroSuccessors
                            · rw [targetIsContractum]
                              have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                                Acc.intro currentScrutinee currentScrutineeSuccessors
                              rw [scrutineeIsSucc] at currentScrutineeSN
                              exact currentInnerSuccContractum currentInnerMotive currentInnerSucc
                                predecessor currentInnerZero
                                (predecessor_isStronglyNormalizing_of_natSucc currentScrutineeSN)
                            · rw [targetIsMotiveStep]
                              exact motiveIH motiveAfter motiveStep
                                (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                                (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                                currentInnerSuccContractum
                            · rw [targetIsZeroStep]
                              exact zeroIH zeroAfter zeroStep
                                (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                                currentInnerSuccContractum
                            · rw [targetIsSuccStep]
                              exact succIH succAfter succStep currentInnerSuccContractum
                            · rw [targetIsScrutineeStep]
                              exact scrutineeIH scrutineeAfter scrutineeStep
                                (Acc.intro currentInnerMotive currentInnerMotiveSuccessors)
                                (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                                (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                                currentInnerSuccContractum)
                      currentSuccTerminates currentInnerZeroContractum)
                currentZeroTerminates currentSuccTerminates currentInnerMotiveContractum))
          currentMotiveTerminates currentZeroTerminates currentSuccTerminates currentContractum))
    scrutineeTerminates)
    motiveTerminates zeroBranchTerminates succBranchTerminates succContractumTerminates

/-- **The natRec redex is strongly normalizing from SN (not necessarily normal) branches** — the
dependent-recursor twin of `natElim_isStronglyNormalizing_of_strongly_normalizing_branches`, identical FOUR-fold
structure with the SUBSTITUTING `natRec` succ-contractum (the universal-substituted-reduct premise so every
congruence arm re-invokes the IH passing the SAME universal premise — no `.inv`). -/
theorem natRec_isStronglyNormalizing_of_strongly_normalizing_branches {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (succContractumTerminates :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentSucc : RawTerm (scope + 2))
        (predecessor currentZero : RawTerm scope), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natRecSuccContractum currentMotive currentSucc predecessor currentZero))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch (.childCons scrutinee .childNil))))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentMotive : RawTerm (scope + 1)} {currentZero : RawTerm scope}
        {currentSucc : RawTerm (scope + 2)},
        IsStronglyNormalizing currentMotive →
        IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
          (∀ (innerMotive : RawTerm (scope + 1)) (innerSucc : RawTerm (scope + 2))
            (predecessor innerZero : RawTerm scope), IsStronglyNormalizing predecessor →
            IsStronglyNormalizing (natRecSuccContractum innerMotive innerSucc predecessor innerZero)) →
          IsStronglyNormalizing
            (.mkGen .gen_natRec ()
              (.childCons currentMotive
                (.childCons currentZero
                  (.childCons currentSucc (.childCons currentScrutinee .childNil))))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentMotive currentZero currentSucc
        currentMotiveTerminates currentZeroTerminates currentSuccTerminates currentContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            ∀ {currentZero : RawTerm scope} {currentSucc : RawTerm (scope + 2)},
              IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
                (∀ (innerMotive' : RawTerm (scope + 1)) (innerSucc : RawTerm (scope + 2))
                  (predecessor innerZero : RawTerm scope), IsStronglyNormalizing predecessor →
                  IsStronglyNormalizing (natRecSuccContractum innerMotive' innerSucc predecessor innerZero)) →
                IsStronglyNormalizing
                  (.mkGen .gen_natRec ()
                    (.childCons innerMotive
                      (.childCons currentZero
                        (.childCons currentSucc (.childCons currentScrutinee .childNil))))))
          (m := fun currentInnerMotive currentInnerMotiveSuccessors motiveIH => by
            intro currentZero currentSucc currentZeroTerminates currentSuccTerminates currentInnerMotiveContractum
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerZero =>
                  ∀ {currentSucc : RawTerm (scope + 2)},
                    IsStronglyNormalizing currentSucc →
                      (∀ (innerMotive' : RawTerm (scope + 1)) (innerSucc : RawTerm (scope + 2))
                        (predecessor innerZero' : RawTerm scope), IsStronglyNormalizing predecessor →
                        IsStronglyNormalizing
                          (natRecSuccContractum innerMotive' innerSucc predecessor innerZero')) →
                      IsStronglyNormalizing
                        (.mkGen .gen_natRec ()
                          (.childCons currentInnerMotive
                            (.childCons innerZero
                              (.childCons currentSucc (.childCons currentScrutinee .childNil))))))
                (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
                  intro currentSucc currentSuccTerminates currentInnerZeroContractum
                  exact
                    Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerSucc =>
                        (∀ (innerMotive' : RawTerm (scope + 1)) (innerSucc' : RawTerm (scope + 2))
                          (predecessor innerZero' : RawTerm scope), IsStronglyNormalizing predecessor →
                          IsStronglyNormalizing
                            (natRecSuccContractum innerMotive' innerSucc' predecessor innerZero')) →
                          IsStronglyNormalizing
                            (.mkGen .gen_natRec ()
                              (.childCons currentInnerMotive
                                (.childCons currentInnerZero
                                  (.childCons innerSucc (.childCons currentScrutinee .childNil))))))
                      (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
                            intro currentInnerSuccContractum
                            apply Acc.intro
                            intro targetTerm natRecStep
                            rcases Step.from_natRec natRecStep with
                              ⟨_scrutineeIsZero, targetIsZero⟩ |
                              ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                              ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                              ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                              ⟨succAfter, targetIsSuccStep, succStep⟩ |
                              ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                            · rw [targetIsZero]
                              exact Acc.intro currentInnerZero currentInnerZeroSuccessors
                            · rw [targetIsContractum]
                              have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                                Acc.intro currentScrutinee currentScrutineeSuccessors
                              rw [scrutineeIsSucc] at currentScrutineeSN
                              exact currentInnerSuccContractum currentInnerMotive currentInnerSucc
                                predecessor currentInnerZero
                                (predecessor_isStronglyNormalizing_of_natSucc currentScrutineeSN)
                            · rw [targetIsMotiveStep]
                              exact motiveIH motiveAfter motiveStep
                                (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                                (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                                currentInnerSuccContractum
                            · rw [targetIsZeroStep]
                              exact zeroIH zeroAfter zeroStep
                                (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                                currentInnerSuccContractum
                            · rw [targetIsSuccStep]
                              exact succIH succAfter succStep currentInnerSuccContractum
                            · rw [targetIsScrutineeStep]
                              exact scrutineeIH scrutineeAfter scrutineeStep
                                (Acc.intro currentInnerMotive currentInnerMotiveSuccessors)
                                (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                                (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                                currentInnerSuccContractum)
                      currentSuccTerminates currentInnerZeroContractum)
                currentZeroTerminates currentSuccTerminates currentInnerMotiveContractum))
          currentMotiveTerminates currentZeroTerminates currentSuccTerminates currentContractum))
    scrutineeTerminates)
    motiveTerminates zeroBranchTerminates succBranchTerminates succContractumTerminates

end StepStar
end FX1Poly.Core
