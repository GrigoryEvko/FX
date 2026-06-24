import FX1Poly.Core.Eliminators.Nat.NatElimNumeralStrongNormalization
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.ApplicationStrongNormalizationForward

/-! # FX1Poly/Core/NatElimReductTrackingStrongNormalization
    — the REDUCT-TRACKING `natElim` cell-SN engine: the satisfiable-premise replacement for the false
      `succContractumSN` / `succBranchSubstClosed` firing obligation (the FTGEN-13.1 keystone engine)

`natElimCellSpine_isStronglyNormalizing_of_normalScrutinee` (in `NatElimNumeralStrongNormalization.lean`)
reduces the cell-SN obligation to a firing obligation `succContractumSN` quantified over ARBITRARY strongly
normalizing branches `(currentMotive, currentZero, currentSucc)`.  That obligation is UNIVERSALLY FALSE at open
scope (the Omega counterexample: substitution does not preserve SN), because the engine exposes only the SN of
the stepped branches, not their PROVENANCE.

This engine fixes that.  It threads, through the three nested `Acc` recursions, a `StepStar` reachability
witness from each ORIGINAL branch to its current (stepped) value.  Its firing obligation `firingContractumSN`
therefore receives `StepStar motive currentMotive`, `StepStar zeroBranch currentZero`, `StepStar succBranch
currentSucc` — exactly the witnesses that make it SATISFIABLE: the substituted contractum at the stepped
branches is a REDUCT of the contractum at the originals (by `StepStar.natElimSuccContractumReduces`), so its SN
follows from the original contractum's SN (`IsStronglyNormalizing.descendStepStar`), and that original
contractum SN is the genuine Tait MEMBERSHIP obligation the value-reducibility arm already carries (CR1).  The
numeral-induction wrapper that discharges `firingContractumSN` this way is the follow-up brick; this file ships
the reachability-threaded engine.

Structurally identical to `_of_normalScrutinee` — three nested `Acc.ndrec` on `(motive, zeroBranch, succBranch)`,
scrutinee fixed normal, the six-way `Step.from_natElim` inversion — except every `Acc` motive carries a leading
`StepStar original current` hypothesis, the SN of a current branch is recovered by `descendStepStar` (not from a
separately-passed SN), and each congruence case extends the reachability witness by `StepStar.trans_compose …
(StepStar.single childStep)` before recursing.

## Zero-axiom verification

`Acc.ndrec` / `Acc.intro` well-founded recursion, the pinned `Step.from_natElim` inversion,
`RawTerm.isStepNormalForm_blocks_step`, `IsStronglyNormalizing.descendStepStar`, and `StepStar.single` /
`StepStar.trans_compose`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration swept by `#audit_namespace FX1Poly.Core` in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- **The reduct-tracking `natElim` cell-SN engine (satisfiable firing premise).**  A `natElim` cell with a
NORMAL scrutinee and strongly-normalizing branches is strongly normalizing, given the REACHABILITY-AWARE firing
obligation `firingContractumSN`: whenever the scrutinee is a successor `natSuccCell predecessor` and the current
branches are reachable from the originals, the substituted succ-iota contractum at the current branches is
strongly normalizing.  Unlike `natElimCellSpine_isStronglyNormalizing_of_normalScrutinee`, whose firing
obligation quantifies over arbitrary SN currents and is therefore unsatisfiable at open scope, this obligation
receives `StepStar` witnesses (`motive ↠ currentMotive` etc.), making it dischargeable from the original
contractum's SN via `StepStar.natElimSuccContractumReduces` + `descendStepStar`.  Three nested `Acc.ndrec` on
the branch accessibilities, each motive carrying its reachability witness. -/
theorem natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (firingContractumSN :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope),
        StepStar motive currentMotive → StepStar zeroBranch currentZero →
        StepStar succBranch currentSucc → scrutinee = natSuccCell predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natElimCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun innerMotive =>
      StepStar motive innerMotive →
      ∀ {currentZero : RawTerm scope} {currentSucc : RawTerm (scope + 2)},
        StepStar zeroBranch currentZero → StepStar succBranch currentSucc →
        IsStronglyNormalizing (natElimCellSpine innerMotive scrutinee currentZero currentSucc))
    (m := fun currentMotive _currentMotiveSuccessors motiveIH => by
      intro motiveChain currentZero currentSucc zeroChain succChain
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerZero =>
            StepStar zeroBranch innerZero →
            ∀ {laterSucc : RawTerm (scope + 2)},
              StepStar succBranch laterSucc →
              IsStronglyNormalizing (natElimCellSpine currentMotive scrutinee innerZero laterSucc))
          (m := fun currentInnerZero _currentInnerZeroSuccessors zeroIH => by
            intro innerZeroChain laterSucc laterSuccChain
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSucc =>
                  StepStar succBranch innerSucc →
                  IsStronglyNormalizing
                    (natElimCellSpine currentMotive scrutinee currentInnerZero innerSucc))
                (m := fun currentInnerSucc _currentInnerSuccSuccessors succIH => by
                  intro innerSuccChain
                  apply Acc.intro
                  intro target step
                  rcases Step.from_natElim step with
                    ⟨_scrutineeIsZero, targetIsZero⟩ |
                    ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                    ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                    ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                    ⟨succAfter, targetIsSuccStep, succStep⟩ |
                    ⟨scrutineeAfter, _targetIsScrutineeStep, scrutineeStep⟩
                  · rw [targetIsZero]
                    exact IsStronglyNormalizing.descendStepStar zeroBranchTerminates innerZeroChain
                  · rw [targetIsContractum]
                    exact firingContractumSN currentMotive currentInnerZero currentInnerSucc
                      predecessor motiveChain innerZeroChain innerSuccChain scrutineeIsSucc
                  · rw [targetIsMotiveStep]
                    exact motiveIH motiveAfter motiveStep
                      (StepStar.trans_compose motiveChain (StepStar.single motiveStep))
                      innerZeroChain innerSuccChain
                  · rw [targetIsZeroStep]
                    exact zeroIH zeroAfter zeroStep
                      (StepStar.trans_compose innerZeroChain (StepStar.single zeroStep))
                      innerSuccChain
                  · rw [targetIsSuccStep]
                    exact succIH succAfter succStep
                      (StepStar.trans_compose innerSuccChain (StepStar.single succStep))
                  · exact absurd scrutineeStep
                      (RawTerm.isStepNormalForm_blocks_step scrutineeNormal scrutineeAfter))
                (IsStronglyNormalizing.descendStepStar succBranchTerminates laterSuccChain))
              laterSuccChain)
          (IsStronglyNormalizing.descendStepStar zeroBranchTerminates zeroChain))
        zeroChain succChain)
    motiveTerminates)
    (StepStar.refl motive) (StepStar.refl zeroBranch) (StepStar.refl succBranch)

end StepStar
end FX1Poly.Core
