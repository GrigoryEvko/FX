import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationMatch
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.ApplicationStrongNormalizationForward
import FX1Poly.Core.Rewriting.Reduction.Step.StepStar

/-! # FX1Poly/Core/MatchReductTrackingStrongNormalization
    — the REDUCT-TRACKING scrutinee-reducing cell-SN engines for the applied-branch matchers
      `optionMatch` / `eitherMatch` (the false-residue-free replacements)

`StrongNormalizationMatch.lean` shipped two `optionMatch` / `eitherMatch` cell-SN engines that consume a
branch-application SN hypothesis of the shape

```
someContractumTerminates : ∀ value, IsStronglyNormalizing value →
  IsStronglyNormalizing (app someBranch value)
```

That hypothesis is UNIVERSALLY FALSE: `app f value` is not strongly normalizing for an arbitrary SN `value`
and a reducible Π-member `f` — a reducible function applied to a merely-SN, non-member argument can diverge
(the `Ω = (λx. x x)(λx. x x)` counterexample, the exact reason Tait reducibility — not SN — is the right
argument predicate).  Threading it to the closed-term consistency leg does NOT discharge it.

This file ships the HONEST replacement, the applied-branch twin of
`listElimCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN`: a scrutinee-reducing
four-fold `Acc.ndrec` whose firing obligation is keyed on the scrutinee REACHING a constructor — the only
`value` the ι ever applies the branch to is the genuine wrapped payload the scrutinee reaches.  So the firing
premise is the satisfiable `originalContractumSN`, e.g. for `eitherMatch`

```
originalLeftContractumSN : ∀ payload, StepStar scrutinee (eitherInl payload) →
  IsStronglyNormalizing (app leftBranch payload)
```

— the CR1 shadow of the Tait member the value-reducibility arm already carries (member ⟹ SN), with NO
arbitrary-SN-value quantification.  At the ι-fire arm the scrutinee reachability identifies the payload, the
ORIGINAL-branch contractum SN comes from `originalContractumSN`, and the stepped-branch contractum is its reduct
by `StepStar.appFunction` (app-head congruence over the branch reachability) + `descendStepStar`.

This file ships:

* `optionMatchCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN` — `optionMatch`
  cell SN from a reducing scrutinee; the none arm lands on the (accessible) current `noneBranch` and carries NO
  firing premise, the some arm consumes `originalSomeContractumSN`.
* `eitherMatchCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN` — `eitherMatch`
  cell SN from a reducing scrutinee; BOTH ι-arms apply a branch, so BOTH `originalLeftContractumSN` and
  `originalRightContractumSN` are consumed, each keyed on the scrutinee reaching the matching injection.

## Zero-axiom verification

Four-fold `Acc.ndrec` / `Acc.intro` well-founded recursion, the pinned `Step.from_optionMatch` /
`Step.from_eitherMatch` inversions, `IsStronglyNormalizing.descendStepStar`, `StepStar.appFunction`, and
`StepStar.trans_compose` / `StepStar.single` / `StepStar.refl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration swept by `#audit_namespace FX1Poly.Core` in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Core
namespace StepStar

open FX1Poly.Axis.Syntax

/-- **The reduct-tracking `optionMatch` cell-SN engine for a REDUCING scrutinee (satisfiable firing premise).**
A four-fold `Acc.ndrec` on (scrutinee, motive, noneBranch, someBranch) threading a `StepStar` reachability
witness through every level; the scrutinee need not be normal.  The firing obligation is the satisfiable
`originalSomeContractumSN`, keyed on the scrutinee REACHING an `optionSome` cell: at the some-ι the scrutinee
reachability identifies the payload, the original `app someBranch payload` SN comes from
`originalSomeContractumSN`, and the stepped-branch contractum is its reduct by `StepStar.appFunction` +
`descendStepStar`.  The none-ι lands on the accessible current `noneBranch`, carrying no firing premise.  The
honest replacement for the false bare-SN firing premise of the `optionMatch` SN engine. -/
theorem optionMatchCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee noneBranch someBranch : RawTerm scope}
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (noneBranchTerminates : IsStronglyNormalizing noneBranch)
    (someBranchTerminates : IsStronglyNormalizing someBranch)
    (originalSomeContractumSN :
      ∀ (payload : RawTerm scope),
        StepStar scrutinee (.mkGen .gen_optionSome () (.childCons payload .childNil)) →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons someBranch (.childCons payload .childNil)))) :
    IsStronglyNormalizing
      (.mkGen .gen_optionMatch ()
        (.childCons motive
          (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      StepStar scrutinee currentScrutinee →
      ∀ {currentMotive : RawTerm (scope + 1)} {currentNone : RawTerm scope} {currentSome : RawTerm scope},
        StepStar motive currentMotive → StepStar noneBranch currentNone →
        StepStar someBranch currentSome →
        IsStronglyNormalizing
          (.mkGen .gen_optionMatch ()
            (.childCons currentMotive
              (.childCons currentNone (.childCons currentSome (.childCons currentScrutinee .childNil))))))
    (m := fun currentScrutinee _currentScrutineeSuccessors scrutineeIH => by
      intro scrutineeReaches currentMotive currentNone currentSome motiveReaches noneReaches someReaches
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            StepStar motive innerMotive →
            ∀ {innerNone : RawTerm scope} {innerSome : RawTerm scope},
              StepStar noneBranch innerNone → StepStar someBranch innerSome →
              IsStronglyNormalizing
                (.mkGen .gen_optionMatch ()
                  (.childCons innerMotive
                    (.childCons innerNone (.childCons innerSome (.childCons currentScrutinee .childNil))))))
          (m := fun currentInnerMotive _currentInnerMotiveSuccessors motiveIH => by
            intro motiveReaches' innerNone innerSome noneReaches' someReaches'
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerNoneVar =>
                  StepStar noneBranch innerNoneVar →
                  ∀ {innerSomeVar : RawTerm scope}, StepStar someBranch innerSomeVar →
                    IsStronglyNormalizing
                      (.mkGen .gen_optionMatch ()
                        (.childCons currentInnerMotive
                          (.childCons innerNoneVar
                            (.childCons innerSomeVar (.childCons currentScrutinee .childNil))))))
                (m := fun currentInnerNone currentInnerNoneSuccessors noneIH => by
                  intro noneReaches'' innerSomeVar someReaches''
                  exact
                    (Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerSomeVar2 =>
                        StepStar someBranch innerSomeVar2 →
                        IsStronglyNormalizing
                          (.mkGen .gen_optionMatch ()
                            (.childCons currentInnerMotive
                              (.childCons currentInnerNone
                                (.childCons innerSomeVar2 (.childCons currentScrutinee .childNil))))))
                      (m := fun currentInnerSome currentInnerSomeSuccessors someIH => by
                        intro someReaches'''
                        apply Acc.intro
                        intro target step
                        rcases Step.from_optionMatch step with
                          ⟨_scrutineeIsNone, targetIsNone⟩ |
                          ⟨payload, scrutineeIsSome, targetIsContractum⟩ |
                          ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                          ⟨noneAfter, targetIsNoneStep, noneStep⟩ |
                          ⟨someAfter, targetIsSomeStep, someStep⟩ |
                          ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                        · rw [targetIsNone]
                          exact Acc.intro currentInnerNone currentInnerNoneSuccessors
                        · rw [targetIsContractum]
                          have scrutineeReachesSome :
                              StepStar scrutinee
                                (.mkGen .gen_optionSome () (.childCons payload .childNil)) := by
                            rw [scrutineeIsSome] at scrutineeReaches; exact scrutineeReaches
                          exact IsStronglyNormalizing.descendStepStar
                            (originalSomeContractumSN payload scrutineeReachesSome)
                            (StepStar.appFunction (argumentTerm := payload) someReaches''')
                        · rw [targetIsMotiveStep]
                          exact motiveIH motiveAfter motiveStep
                            (StepStar.trans_compose motiveReaches' (StepStar.single motiveStep))
                            noneReaches'' someReaches'''
                        · rw [targetIsNoneStep]
                          exact noneIH noneAfter noneStep
                            (StepStar.trans_compose noneReaches'' (StepStar.single noneStep))
                            someReaches'''
                        · rw [targetIsSomeStep]
                          exact someIH someAfter someStep
                            (StepStar.trans_compose someReaches''' (StepStar.single someStep))
                        · rw [targetIsScrutineeStep]
                          exact scrutineeIH scrutineeAfter scrutineeStep
                            (StepStar.trans_compose scrutineeReaches (StepStar.single scrutineeStep))
                            motiveReaches' noneReaches'' someReaches''')
                      (IsStronglyNormalizing.descendStepStar someBranchTerminates someReaches''))
                    someReaches'')
                (IsStronglyNormalizing.descendStepStar noneBranchTerminates noneReaches'))
              noneReaches' someReaches')
          (IsStronglyNormalizing.descendStepStar motiveTerminates motiveReaches))
        motiveReaches noneReaches someReaches)
    scrutineeTerminates)
    (StepStar.refl scrutinee) (StepStar.refl motive) (StepStar.refl noneBranch) (StepStar.refl someBranch)

/-- **The reduct-tracking `eitherMatch` cell-SN engine for a REDUCING scrutinee (satisfiable firing premise).**
Symmetric to the `optionMatch` engine, but BOTH ι-arms apply a branch (no passive base), so BOTH
`originalLeftContractumSN` and `originalRightContractumSN` are consumed — each keyed on the scrutinee REACHING
the matching injection (`StepStar scrutinee (eitherInl payload)` / `(eitherInr payload)`).  At each ι-fire arm
the scrutinee reachability identifies the payload, the original-branch contractum SN comes from the
corresponding premise, and the stepped-branch contractum is its reduct by `StepStar.appFunction` (over the
matching branch reachability) + `descendStepStar`.  The honest, false-residue-free `eitherMatch` SN engine. -/
theorem eitherMatchCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee leftBranch rightBranch : RawTerm scope}
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (leftBranchTerminates : IsStronglyNormalizing leftBranch)
    (rightBranchTerminates : IsStronglyNormalizing rightBranch)
    (originalLeftContractumSN :
      ∀ (payload : RawTerm scope),
        StepStar scrutinee (.mkGen .gen_eitherInl () (.childCons payload .childNil)) →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons leftBranch (.childCons payload .childNil))))
    (originalRightContractumSN :
      ∀ (payload : RawTerm scope),
        StepStar scrutinee (.mkGen .gen_eitherInr () (.childCons payload .childNil)) →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons rightBranch (.childCons payload .childNil)))) :
    IsStronglyNormalizing
      (.mkGen .gen_eitherMatch ()
        (.childCons motive
          (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      StepStar scrutinee currentScrutinee →
      ∀ {currentMotive : RawTerm (scope + 1)} {currentLeft : RawTerm scope} {currentRight : RawTerm scope},
        StepStar motive currentMotive → StepStar leftBranch currentLeft →
        StepStar rightBranch currentRight →
        IsStronglyNormalizing
          (.mkGen .gen_eitherMatch ()
            (.childCons currentMotive
              (.childCons currentLeft (.childCons currentRight (.childCons currentScrutinee .childNil))))))
    (m := fun currentScrutinee _currentScrutineeSuccessors scrutineeIH => by
      intro scrutineeReaches currentMotive currentLeft currentRight motiveReaches leftReaches rightReaches
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            StepStar motive innerMotive →
            ∀ {innerLeft : RawTerm scope} {innerRight : RawTerm scope},
              StepStar leftBranch innerLeft → StepStar rightBranch innerRight →
              IsStronglyNormalizing
                (.mkGen .gen_eitherMatch ()
                  (.childCons innerMotive
                    (.childCons innerLeft (.childCons innerRight (.childCons currentScrutinee .childNil))))))
          (m := fun currentInnerMotive _currentInnerMotiveSuccessors motiveIH => by
            intro motiveReaches' innerLeft innerRight leftReaches' rightReaches'
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerLeftVar =>
                  StepStar leftBranch innerLeftVar →
                  ∀ {innerRightVar : RawTerm scope}, StepStar rightBranch innerRightVar →
                    IsStronglyNormalizing
                      (.mkGen .gen_eitherMatch ()
                        (.childCons currentInnerMotive
                          (.childCons innerLeftVar
                            (.childCons innerRightVar (.childCons currentScrutinee .childNil))))))
                (m := fun currentInnerLeft currentInnerLeftSuccessors leftIH => by
                  intro leftReaches'' innerRightVar rightReaches''
                  exact
                    (Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerRightVar2 =>
                        StepStar rightBranch innerRightVar2 →
                        IsStronglyNormalizing
                          (.mkGen .gen_eitherMatch ()
                            (.childCons currentInnerMotive
                              (.childCons currentInnerLeft
                                (.childCons innerRightVar2 (.childCons currentScrutinee .childNil))))))
                      (m := fun currentInnerRight currentInnerRightSuccessors rightIH => by
                        intro rightReaches'''
                        apply Acc.intro
                        intro target step
                        rcases Step.from_eitherMatch step with
                          ⟨payload, scrutineeIsInl, targetIsLeftContractum⟩ |
                          ⟨payload, scrutineeIsInr, targetIsRightContractum⟩ |
                          ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                          ⟨leftAfter, targetIsLeftStep, leftStep⟩ |
                          ⟨rightAfter, targetIsRightStep, rightStep⟩ |
                          ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                        · rw [targetIsLeftContractum]
                          have scrutineeReachesInl :
                              StepStar scrutinee
                                (.mkGen .gen_eitherInl () (.childCons payload .childNil)) := by
                            rw [scrutineeIsInl] at scrutineeReaches; exact scrutineeReaches
                          exact IsStronglyNormalizing.descendStepStar
                            (originalLeftContractumSN payload scrutineeReachesInl)
                            (StepStar.appFunction (argumentTerm := payload) leftReaches'')
                        · rw [targetIsRightContractum]
                          have scrutineeReachesInr :
                              StepStar scrutinee
                                (.mkGen .gen_eitherInr () (.childCons payload .childNil)) := by
                            rw [scrutineeIsInr] at scrutineeReaches; exact scrutineeReaches
                          exact IsStronglyNormalizing.descendStepStar
                            (originalRightContractumSN payload scrutineeReachesInr)
                            (StepStar.appFunction (argumentTerm := payload) rightReaches''')
                        · rw [targetIsMotiveStep]
                          exact motiveIH motiveAfter motiveStep
                            (StepStar.trans_compose motiveReaches' (StepStar.single motiveStep))
                            leftReaches'' rightReaches'''
                        · rw [targetIsLeftStep]
                          exact leftIH leftAfter leftStep
                            (StepStar.trans_compose leftReaches'' (StepStar.single leftStep))
                            rightReaches'''
                        · rw [targetIsRightStep]
                          exact rightIH rightAfter rightStep
                            (StepStar.trans_compose rightReaches''' (StepStar.single rightStep))
                        · rw [targetIsScrutineeStep]
                          exact scrutineeIH scrutineeAfter scrutineeStep
                            (StepStar.trans_compose scrutineeReaches (StepStar.single scrutineeStep))
                            motiveReaches' leftReaches'' rightReaches''')
                      (IsStronglyNormalizing.descendStepStar rightBranchTerminates rightReaches''))
                    rightReaches'')
                (IsStronglyNormalizing.descendStepStar leftBranchTerminates leftReaches'))
              leftReaches' rightReaches')
          (IsStronglyNormalizing.descendStepStar motiveTerminates motiveReaches))
        motiveReaches leftReaches rightReaches)
    scrutineeTerminates)
    (StepStar.refl scrutinee) (StepStar.refl motive) (StepStar.refl leftBranch) (StepStar.refl rightBranch)

end StepStar
end FX1Poly.Core
