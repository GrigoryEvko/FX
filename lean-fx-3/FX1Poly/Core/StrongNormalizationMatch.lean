import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationIotaRedexes

/-! # FX1Poly/Core/StrongNormalizationMatch
    — the non-recursive applied-branch eliminator iota-redex SN: optionMatch / eitherMatch

`StrongNormalizationNatElim.lean` / `StrongNormalizationListElim.lean` shipped the firing-case
(`_of_normal_branches`) iota-redex SN for the RECURSIVE eliminators (`natElim` / `natRec` / `listElim`), whose
ι-contractum contains a recursive call.  `boolElim` / `idJ` / `idStrictRec` (PASSIVE-branch contractum) are in
`StrongNormalizationIotaRedexes.lean`.  This file does the third shape — the NON-RECURSIVE APPLIED-branch
matchers `optionMatch` / `eitherMatch`, whose ι-rules apply the branch to the wrapped value with no recursive
call:

```
optionMatch (optionSome value) noneBranch someBranch ↝ app someBranch value
eitherMatch (eitherInl value) leftBranch rightBranch ↝ app leftBranch value
eitherMatch (eitherInr value) leftBranch rightBranch ↝ app rightBranch value
```

The contractum is a single application `app branch value` — no recursive eliminator call, so the
`*ContractumTerminates` hypothesis is parameterized only over the wrapped `value`'s SN (no IH on a smaller
scrutinee).  This is the normal-branch firing-case complement of the shipped neutral-branch
`optionMatchSome_isStronglyNormalizing_of_neutral_someBranch` / `eitherMatch…_of_neutral_…Branch`.

This file ships:

* `value_isStronglyNormalizing_of_optionSome` / `_of_eitherInl` / `_of_eitherInr` — the three one-child value
  subterm-SN lemmas (the wrapped value of a strongly-normalizing `optionSome` / `eitherInl` / `eitherInr` is
  strongly normalizing), the `gen_optionSome`/`gen_eitherInl`/`gen_eitherInr` mirrors of
  `predecessor_isStronglyNormalizing_of_natSucc`.
* `optionMatch_isStronglyNormalizing_of_normal_branches` — `optionMatch` redex SN with normal branches + the
  some-contractum `app someBranch value` SN for every SN value (the none arm lands on the normal `noneBranch`).
* `eitherMatch_isStronglyNormalizing_of_normal_branches` — `eitherMatch` redex SN with normal branches + BOTH
  the left- and right-contractum `app …Branch value` SN for every SN value (no passive base arm — both
  `eitherMatch` ι-arms apply a branch).

## Zero-axiom verification

The value subterm lemmas are `Acc` well-founded recursion generalized over the constructor term (each value
step lifts via `StepChildren.here`), mirroring `predecessor_isStronglyNormalizing_of_natSucc`.  The redex SN
is `Acc.ndrec` on the scrutinee; `Step.from_optionMatch` / `Step.from_eitherMatch` split the six arms
(Phase-Z motive shape: motive first under one binder, scrutinee last) — the ι-fire arms land on the applied
contractum (discharged by `*ContractumTerminates` at the value subterm-SN), scrutinee-congruence by the
induction hypothesis, and the motive- + branch-congruences are impossible (normal motive + branches).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- **The wrapped value of a strongly-normalizing `optionSome` is strongly normalizing.**  One-child
subterm-SN lemma; the `gen_optionSome` mirror of `predecessor_isStronglyNormalizing_of_natSucc`. -/
theorem value_isStronglyNormalizing_of_optionSome {scope : Nat}
    {value : RawTerm scope}
    (someTerminates :
      IsStronglyNormalizing (.mkGen .gen_optionSome () (.childCons value .childNil) : RawTerm scope)) :
    IsStronglyNormalizing value := by
  suffices general :
      ∀ {someTerm : RawTerm scope}, Acc StepSuccessor someTerm →
        ∀ {currentValue : RawTerm scope},
          someTerm = .mkGen .gen_optionSome () (.childCons currentValue .childNil) →
          Acc StepSuccessor currentValue from
    general someTerminates rfl
  intro someTerm someAccessible
  induction someAccessible with
  | intro someWitness _somePredecessors someInductiveHypothesis =>
      intro currentValue witnessEq
      subst witnessEq
      apply Acc.intro
      intro valueAfter valueStep
      have congruenceLift :
          Step (.mkGen .gen_optionSome () (.childCons currentValue .childNil) : RawTerm scope)
            (.mkGen .gen_optionSome () (.childCons valueAfter .childNil) : RawTerm scope) :=
        Step.cong .gen_optionSome () (StepChildren.here .childNil valueStep)
      exact someInductiveHypothesis
        (.mkGen .gen_optionSome () (.childCons valueAfter .childNil)) congruenceLift rfl

/-- **The wrapped value of a strongly-normalizing `eitherInl` is strongly normalizing.** -/
theorem value_isStronglyNormalizing_of_eitherInl {scope : Nat}
    {value : RawTerm scope}
    (inlTerminates :
      IsStronglyNormalizing (.mkGen .gen_eitherInl () (.childCons value .childNil) : RawTerm scope)) :
    IsStronglyNormalizing value := by
  suffices general :
      ∀ {inlTerm : RawTerm scope}, Acc StepSuccessor inlTerm →
        ∀ {currentValue : RawTerm scope},
          inlTerm = .mkGen .gen_eitherInl () (.childCons currentValue .childNil) →
          Acc StepSuccessor currentValue from
    general inlTerminates rfl
  intro inlTerm inlAccessible
  induction inlAccessible with
  | intro inlWitness _inlPredecessors inlInductiveHypothesis =>
      intro currentValue witnessEq
      subst witnessEq
      apply Acc.intro
      intro valueAfter valueStep
      have congruenceLift :
          Step (.mkGen .gen_eitherInl () (.childCons currentValue .childNil) : RawTerm scope)
            (.mkGen .gen_eitherInl () (.childCons valueAfter .childNil) : RawTerm scope) :=
        Step.cong .gen_eitherInl () (StepChildren.here .childNil valueStep)
      exact inlInductiveHypothesis
        (.mkGen .gen_eitherInl () (.childCons valueAfter .childNil)) congruenceLift rfl

/-- **The wrapped value of a strongly-normalizing `eitherInr` is strongly normalizing.** -/
theorem value_isStronglyNormalizing_of_eitherInr {scope : Nat}
    {value : RawTerm scope}
    (inrTerminates :
      IsStronglyNormalizing (.mkGen .gen_eitherInr () (.childCons value .childNil) : RawTerm scope)) :
    IsStronglyNormalizing value := by
  suffices general :
      ∀ {inrTerm : RawTerm scope}, Acc StepSuccessor inrTerm →
        ∀ {currentValue : RawTerm scope},
          inrTerm = .mkGen .gen_eitherInr () (.childCons currentValue .childNil) →
          Acc StepSuccessor currentValue from
    general inrTerminates rfl
  intro inrTerm inrAccessible
  induction inrAccessible with
  | intro inrWitness _inrPredecessors inrInductiveHypothesis =>
      intro currentValue witnessEq
      subst witnessEq
      apply Acc.intro
      intro valueAfter valueStep
      have congruenceLift :
          Step (.mkGen .gen_eitherInr () (.childCons currentValue .childNil) : RawTerm scope)
            (.mkGen .gen_eitherInr () (.childCons valueAfter .childNil) : RawTerm scope) :=
        Step.cong .gen_eitherInr () (StepChildren.here .childNil valueStep)
      exact inrInductiveHypothesis
        (.mkGen .gen_eitherInr () (.childCons valueAfter .childNil)) congruenceLift rfl

/-- **The optionMatch iota-redex is strongly normalizing.**  With both branches normal and the some-contractum
`app someBranch value` strongly normalizing for every strongly-normalizing value, an `optionMatch` redex with
a strongly-normalizing scrutinee is strongly normalizing.  Phase-Z motive shape (motive first under one
binder, scrutinee last).  `Acc.ndrec` on the scrutinee; `Step.from_optionMatch` gives the six arms: ι-none →
the normal `noneBranch`; ι-some → the applied contractum (discharged by `someContractumTerminates` at the
`optionSome` value subterm-SN); scrutinee-congruence → the IH; motive- + branch-congruences → impossible by
normality. -/
theorem optionMatch_isStronglyNormalizing_of_normal_branches {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee noneBranch someBranch : RawTerm scope}
    (motiveHasNoStep : ∀ targetMotive : RawTerm (scope + 1), Step motive targetMotive → False)
    (noneBranchHasNoStep : ∀ targetNone : RawTerm scope, Step noneBranch targetNone → False)
    (someBranchHasNoStep : ∀ targetSome : RawTerm scope, Step someBranch targetSome → False)
    (someContractumTerminates :
      ∀ {value : RawTerm scope}, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons someBranch (.childCons value .childNil)) : RawTerm scope))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_optionMatch ()
        (.childCons motive
          (.childCons noneBranch
            (.childCons someBranch (.childCons scrutinee .childNil)))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch
              (.childCons someBranch (.childCons currentScrutinee .childNil)))) :
          RawTerm scope))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch
              (.childCons someBranch (.childCons currentScrutinee .childNil)))) :
          RawTerm scope)
        (fun targetTerm matchStep => by
          rcases Step.from_optionMatch matchStep with
            ⟨_scrutineeIsNone, targetIsNone⟩ |
            ⟨value, scrutineeIsSome, targetIsContractum⟩ |
            ⟨motiveAfter, _targetIsMotiveStep, motiveStep⟩ |
            ⟨noneAfter, _targetIsNoneStep, noneStep⟩ |
            ⟨someAfter, _targetIsSomeStep, someStep⟩ |
            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
          · rw [targetIsNone]
            exact isStronglyNormalizing_of_noStep noneBranchHasNoStep
          · rw [targetIsContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsSome] at currentScrutineeSN
            exact someContractumTerminates
              (value_isStronglyNormalizing_of_optionSome currentScrutineeSN)
          · exact absurd motiveStep (motiveHasNoStep motiveAfter)
          · exact absurd noneStep (noneBranchHasNoStep noneAfter)
          · exact absurd someStep (someBranchHasNoStep someAfter)
          · rw [targetIsScrutineeStep]
            exact scrutineeIH scrutineeAfter scrutineeStep))
    scrutineeTerminates

/-- **The eitherMatch iota-redex is strongly normalizing.**  With both branches normal and BOTH the
left-contractum `app leftBranch value` and right-contractum `app rightBranch value` strongly normalizing for
every strongly-normalizing value, an `eitherMatch` redex with a strongly-normalizing scrutinee is strongly
normalizing.  Unlike `optionMatch`, both ι-arms apply a branch (no passive base), so both contractum
hypotheses are consumed, each at the corresponding `eitherInl` / `eitherInr` value subterm-SN. -/
theorem eitherMatch_isStronglyNormalizing_of_normal_branches {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee leftBranch rightBranch : RawTerm scope}
    (motiveHasNoStep : ∀ targetMotive : RawTerm (scope + 1), Step motive targetMotive → False)
    (leftBranchHasNoStep : ∀ targetLeft : RawTerm scope, Step leftBranch targetLeft → False)
    (rightBranchHasNoStep : ∀ targetRight : RawTerm scope, Step rightBranch targetRight → False)
    (leftContractumTerminates :
      ∀ {value : RawTerm scope}, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil)) : RawTerm scope))
    (rightContractumTerminates :
      ∀ {value : RawTerm scope}, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil)) : RawTerm scope))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_eitherMatch ()
        (.childCons motive
          (.childCons leftBranch
            (.childCons rightBranch (.childCons scrutinee .childNil)))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_eitherMatch ()
          (.childCons motive
            (.childCons leftBranch
              (.childCons rightBranch (.childCons currentScrutinee .childNil)))) :
          RawTerm scope))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_eitherMatch ()
          (.childCons motive
            (.childCons leftBranch
              (.childCons rightBranch (.childCons currentScrutinee .childNil)))) :
          RawTerm scope)
        (fun targetTerm matchStep => by
          rcases Step.from_eitherMatch matchStep with
            ⟨value, scrutineeIsInl, targetIsLeftContractum⟩ |
            ⟨value, scrutineeIsInr, targetIsRightContractum⟩ |
            ⟨motiveAfter, _targetIsMotiveStep, motiveStep⟩ |
            ⟨leftAfter, _targetIsLeftStep, leftStep⟩ |
            ⟨rightAfter, _targetIsRightStep, rightStep⟩ |
            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
          · rw [targetIsLeftContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsInl] at currentScrutineeSN
            exact leftContractumTerminates
              (value_isStronglyNormalizing_of_eitherInl currentScrutineeSN)
          · rw [targetIsRightContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsInr] at currentScrutineeSN
            exact rightContractumTerminates
              (value_isStronglyNormalizing_of_eitherInr currentScrutineeSN)
          · exact absurd motiveStep (motiveHasNoStep motiveAfter)
          · exact absurd leftStep (leftBranchHasNoStep leftAfter)
          · exact absurd rightStep (rightBranchHasNoStep rightAfter)
          · rw [targetIsScrutineeStep]
            exact scrutineeIH scrutineeAfter scrutineeStep))
    scrutineeTerminates

/-- **The optionMatch redex is strongly normalizing from SN (not necessarily normal) branches.**  The SN-branch
strengthening of `optionMatch_isStronglyNormalizing_of_normal_branches`, the analogue of
`boolElim_isStronglyNormalizing_of_strongly_normalizing_branches`.  Required for eliminator REDUCIBILITY: in the
Tait/data-candidate argument the branches are MEMBERS (hence SN) but not normal.  A triple nested accessibility
induction on `(scrutinee, noneBranch, someBranch)`; the some-contractum SN hypothesis
`someContractumTerminates : ∀ value, SN value → SN (app someBranch value)` is THREADED through the someBranch
induction — when `someBranch ↝ someAfter`, the updated hypothesis is recovered via app-head congruence and
`IsStronglyNormalizing.inv` (`app someBranch value ↝ app someAfter value`, so the contractum SN descends). -/
theorem optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee noneBranch someBranch : RawTerm scope}
    (someContractumTerminates :
      ∀ value : RawTerm scope, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons someBranch (.childCons value .childNil))))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (noneBranchTerminates : IsStronglyNormalizing noneBranch)
    (someBranchTerminates : IsStronglyNormalizing someBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_optionMatch ()
        (.childCons motive
          (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentMotive : RawTerm (scope + 1)} {currentNone currentSome : RawTerm scope},
        IsStronglyNormalizing currentMotive →
        IsStronglyNormalizing currentNone → IsStronglyNormalizing currentSome →
          (∀ value : RawTerm scope, IsStronglyNormalizing value →
            IsStronglyNormalizing
              (.mkGen .gen_app () (.childCons currentSome (.childCons value .childNil)))) →
          IsStronglyNormalizing
            (.mkGen .gen_optionMatch ()
              (.childCons currentMotive
                (.childCons currentNone
                  (.childCons currentSome (.childCons currentScrutinee .childNil))))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentMotive currentNone currentSome currentMotiveTerminates
        currentNoneTerminates currentSomeTerminates currentSomeContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            ∀ {innerNone innerSome : RawTerm scope},
              IsStronglyNormalizing innerNone → IsStronglyNormalizing innerSome →
                (∀ value : RawTerm scope, IsStronglyNormalizing value →
                  IsStronglyNormalizing
                    (.mkGen .gen_app () (.childCons innerSome (.childCons value .childNil)))) →
                IsStronglyNormalizing
                  (.mkGen .gen_optionMatch ()
                    (.childCons innerMotive
                      (.childCons innerNone
                        (.childCons innerSome (.childCons currentScrutinee .childNil))))))
          (m := fun currentInnerMotive currentInnerMotiveSuccessors motiveIH => by
            intro innerNone innerSome innerNoneTerminates innerSomeTerminates innerSomeContractum
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerNone' =>
                  ∀ {innerSome' : RawTerm scope},
                    IsStronglyNormalizing innerSome' →
                      (∀ value : RawTerm scope, IsStronglyNormalizing value →
                        IsStronglyNormalizing
                          (.mkGen .gen_app ()
                            (.childCons innerSome' (.childCons value .childNil)))) →
                        IsStronglyNormalizing
                          (.mkGen .gen_optionMatch ()
                            (.childCons currentInnerMotive
                              (.childCons innerNone'
                                (.childCons innerSome'
                                  (.childCons currentScrutinee .childNil))))))
                (m := fun currentInnerNone currentInnerNoneSuccessors noneIH => by
                  intro innerSome' innerSomeTerminates' innerSomeContractum'
                  exact
                    Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerSome'' =>
                        (∀ value : RawTerm scope, IsStronglyNormalizing value →
                          IsStronglyNormalizing
                            (.mkGen .gen_app ()
                              (.childCons innerSome'' (.childCons value .childNil)))) →
                          IsStronglyNormalizing
                            (.mkGen .gen_optionMatch ()
                              (.childCons currentInnerMotive
                                (.childCons currentInnerNone
                                  (.childCons innerSome''
                                    (.childCons currentScrutinee .childNil))))))
                      (m := fun currentInnerSome currentInnerSomeSuccessors someIH => by
                            intro currentInnerSomeContractum
                            apply Acc.intro
                            intro targetTerm matchStep
                            rcases Step.from_optionMatch matchStep with
                              ⟨_scrutineeIsNone, targetIsNone⟩ |
                              ⟨value, scrutineeIsSome, targetIsContractum⟩ |
                              ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                              ⟨noneAfter, targetIsNoneStep, noneStep⟩ |
                              ⟨someAfter, targetIsSomeStep, someStep⟩ |
                              ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                            · rw [targetIsNone]
                              exact Acc.intro currentInnerNone currentInnerNoneSuccessors
                            · rw [targetIsContractum]
                              have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                                Acc.intro currentScrutinee currentScrutineeSuccessors
                              rw [scrutineeIsSome] at currentScrutineeSN
                              exact currentInnerSomeContractum value
                                (value_isStronglyNormalizing_of_optionSome currentScrutineeSN)
                            · rw [targetIsMotiveStep]
                              exact motiveIH motiveAfter motiveStep
                                (Acc.intro currentInnerNone currentInnerNoneSuccessors)
                                (Acc.intro currentInnerSome currentInnerSomeSuccessors)
                                currentInnerSomeContractum
                            · rw [targetIsNoneStep]
                              exact noneIH noneAfter noneStep
                                (Acc.intro currentInnerSome currentInnerSomeSuccessors)
                                currentInnerSomeContractum
                            · rw [targetIsSomeStep]
                              exact someIH someAfter someStep
                                (fun value valueTerminates =>
                                  (currentInnerSomeContractum value valueTerminates).inv
                                    (Step.cong .gen_app ()
                                      (StepChildren.here
                                        (.childCons value .childNil : RawTermChildren [0] scope)
                                        someStep)))
                            · rw [targetIsScrutineeStep]
                              exact scrutineeIH scrutineeAfter scrutineeStep
                                (Acc.intro currentInnerMotive currentInnerMotiveSuccessors)
                                (Acc.intro currentInnerNone currentInnerNoneSuccessors)
                                (Acc.intro currentInnerSome currentInnerSomeSuccessors)
                                currentInnerSomeContractum)
                      innerSomeTerminates' innerSomeContractum')
                innerNoneTerminates innerSomeTerminates innerSomeContractum))
          currentMotiveTerminates currentNoneTerminates currentSomeTerminates currentSomeContractum))
    scrutineeTerminates)
    motiveTerminates noneBranchTerminates someBranchTerminates someContractumTerminates

/-- **The eitherMatch redex is strongly normalizing from SN (not necessarily normal) branches.**  Symmetric to
`optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches`, but BOTH ι-arms apply a branch, so BOTH the
left- and right-contractum SN hypotheses are threaded — the left through the leftBranch (middle) induction, the
right through the rightBranch (inner) induction, each updated under its own congruence via app-head congruence +
`IsStronglyNormalizing.inv`. -/
theorem eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee leftBranch rightBranch : RawTerm scope}
    (leftContractumTerminates :
      ∀ value : RawTerm scope, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil))))
    (rightContractumTerminates :
      ∀ value : RawTerm scope, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil))))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (leftBranchTerminates : IsStronglyNormalizing leftBranch)
    (rightBranchTerminates : IsStronglyNormalizing rightBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_eitherMatch ()
        (.childCons motive
          (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentMotive : RawTerm (scope + 1)} {currentLeft currentRight : RawTerm scope},
        IsStronglyNormalizing currentMotive →
        IsStronglyNormalizing currentLeft → IsStronglyNormalizing currentRight →
          (∀ value : RawTerm scope, IsStronglyNormalizing value →
            IsStronglyNormalizing
              (.mkGen .gen_app () (.childCons currentLeft (.childCons value .childNil)))) →
          (∀ value : RawTerm scope, IsStronglyNormalizing value →
            IsStronglyNormalizing
              (.mkGen .gen_app () (.childCons currentRight (.childCons value .childNil)))) →
          IsStronglyNormalizing
            (.mkGen .gen_eitherMatch ()
              (.childCons currentMotive
                (.childCons currentLeft
                  (.childCons currentRight (.childCons currentScrutinee .childNil))))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentMotive currentLeft currentRight currentMotiveTerminates
        currentLeftTerminates currentRightTerminates
        currentLeftContractum currentRightContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            ∀ {innerLeft innerRight : RawTerm scope},
              IsStronglyNormalizing innerLeft → IsStronglyNormalizing innerRight →
                (∀ value : RawTerm scope, IsStronglyNormalizing value →
                  IsStronglyNormalizing
                    (.mkGen .gen_app () (.childCons innerLeft (.childCons value .childNil)))) →
                (∀ value : RawTerm scope, IsStronglyNormalizing value →
                  IsStronglyNormalizing
                    (.mkGen .gen_app () (.childCons innerRight (.childCons value .childNil)))) →
                IsStronglyNormalizing
                  (.mkGen .gen_eitherMatch ()
                    (.childCons innerMotive
                      (.childCons innerLeft
                        (.childCons innerRight (.childCons currentScrutinee .childNil))))))
          (m := fun currentInnerMotive currentInnerMotiveSuccessors motiveIH => by
            intro innerLeft innerRight innerLeftTerminates innerRightTerminates
              innerLeftContractum innerRightContractum
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerLeft' =>
                  ∀ {innerRight' : RawTerm scope},
                    IsStronglyNormalizing innerRight' →
                      (∀ value : RawTerm scope, IsStronglyNormalizing value →
                        IsStronglyNormalizing
                          (.mkGen .gen_app ()
                            (.childCons innerLeft' (.childCons value .childNil)))) →
                      (∀ value : RawTerm scope, IsStronglyNormalizing value →
                        IsStronglyNormalizing
                          (.mkGen .gen_app ()
                            (.childCons innerRight' (.childCons value .childNil)))) →
                        IsStronglyNormalizing
                          (.mkGen .gen_eitherMatch ()
                            (.childCons currentInnerMotive
                              (.childCons innerLeft'
                                (.childCons innerRight'
                                  (.childCons currentScrutinee .childNil))))))
                (m := fun currentInnerLeft currentInnerLeftSuccessors leftIH => by
                  intro innerRight' innerRightTerminates' currentInnerLeftContractum
                    innerRightContractum'
                  exact
                    Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerRight'' =>
                        (∀ value : RawTerm scope, IsStronglyNormalizing value →
                          IsStronglyNormalizing
                            (.mkGen .gen_app ()
                              (.childCons currentInnerLeft (.childCons value .childNil)))) →
                          (∀ value : RawTerm scope, IsStronglyNormalizing value →
                            IsStronglyNormalizing
                              (.mkGen .gen_app ()
                                (.childCons innerRight'' (.childCons value .childNil)))) →
                            IsStronglyNormalizing
                              (.mkGen .gen_eitherMatch ()
                                (.childCons currentInnerMotive
                                  (.childCons currentInnerLeft
                                    (.childCons innerRight''
                                      (.childCons currentScrutinee .childNil))))))
                      (m := fun currentInnerRight currentInnerRightSuccessors rightIH => by
                            intro currentInnerLeftContractum' currentInnerRightContractum
                            apply Acc.intro
                            intro targetTerm matchStep
                            rcases Step.from_eitherMatch matchStep with
                              ⟨value, scrutineeIsInl, targetIsLeftContractum⟩ |
                              ⟨value, scrutineeIsInr, targetIsRightContractum⟩ |
                              ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                              ⟨leftAfter, targetIsLeftStep, leftStep⟩ |
                              ⟨rightAfter, targetIsRightStep, rightStep⟩ |
                              ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                            · rw [targetIsLeftContractum]
                              have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                                Acc.intro currentScrutinee currentScrutineeSuccessors
                              rw [scrutineeIsInl] at currentScrutineeSN
                              exact currentInnerLeftContractum' value
                                (value_isStronglyNormalizing_of_eitherInl currentScrutineeSN)
                            · rw [targetIsRightContractum]
                              have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                                Acc.intro currentScrutinee currentScrutineeSuccessors
                              rw [scrutineeIsInr] at currentScrutineeSN
                              exact currentInnerRightContractum value
                                (value_isStronglyNormalizing_of_eitherInr currentScrutineeSN)
                            · rw [targetIsMotiveStep]
                              exact motiveIH motiveAfter motiveStep
                                (Acc.intro currentInnerLeft currentInnerLeftSuccessors)
                                (Acc.intro currentInnerRight currentInnerRightSuccessors)
                                currentInnerLeftContractum' currentInnerRightContractum
                            · rw [targetIsLeftStep]
                              exact leftIH leftAfter leftStep
                                (Acc.intro currentInnerRight currentInnerRightSuccessors)
                                (fun value valueTerminates =>
                                  (currentInnerLeftContractum' value valueTerminates).inv
                                    (Step.cong .gen_app ()
                                      (StepChildren.here
                                        (.childCons value .childNil : RawTermChildren [0] scope)
                                        leftStep)))
                                currentInnerRightContractum
                            · rw [targetIsRightStep]
                              exact rightIH rightAfter rightStep
                                currentInnerLeftContractum'
                                (fun value valueTerminates =>
                                  (currentInnerRightContractum value valueTerminates).inv
                                    (Step.cong .gen_app ()
                                      (StepChildren.here
                                        (.childCons value .childNil : RawTermChildren [0] scope)
                                        rightStep)))
                            · rw [targetIsScrutineeStep]
                              exact scrutineeIH scrutineeAfter scrutineeStep
                                (Acc.intro currentInnerMotive currentInnerMotiveSuccessors)
                                (Acc.intro currentInnerLeft currentInnerLeftSuccessors)
                                (Acc.intro currentInnerRight currentInnerRightSuccessors)
                                currentInnerLeftContractum' currentInnerRightContractum)
                      innerRightTerminates' currentInnerLeftContractum innerRightContractum')
                innerLeftTerminates innerRightTerminates innerLeftContractum innerRightContractum))
          currentMotiveTerminates currentLeftTerminates currentRightTerminates
            currentLeftContractum currentRightContractum))
    scrutineeTerminates)
    motiveTerminates leftBranchTerminates rightBranchTerminates
      leftContractumTerminates rightContractumTerminates

end StepStar
end FX1Poly.Core
