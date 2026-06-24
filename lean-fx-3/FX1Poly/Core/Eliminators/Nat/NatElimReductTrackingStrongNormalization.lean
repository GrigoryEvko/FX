import FX1Poly.Core.Eliminators.Nat.NatElimNumeralStrongNormalization
import FX1Poly.Core.Eliminators.Nat.NatElimSuccContractumReductionCongruence
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

/-- **The reduct-tracking `natRec` cell-SN engine (satisfiable firing premise) — the `natRec` twin.**  Verbatim
mirror of `natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability` with `natElimCellSpine`
swapped for `natRecCellSpine` and the inversion `Step.from_natElim` for `Step.from_natRec` (the two recursors
share the v2 substrate's arity-4 metadata and six-way inversion).  The reachability thread through the three
nested `Acc.ndrec` makes the firing obligation `firingContractumSN` satisfiable from the original contractum's SN
via `StepStar.natRecSuccContractumReduces` + `IsStronglyNormalizing.descendStepStar`. -/
theorem natRecCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability {scope : Nat}
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
              (natRecCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun innerMotive =>
      StepStar motive innerMotive →
      ∀ {currentZero : RawTerm scope} {currentSucc : RawTerm (scope + 2)},
        StepStar zeroBranch currentZero → StepStar succBranch currentSucc →
        IsStronglyNormalizing (natRecCellSpine innerMotive scrutinee currentZero currentSucc))
    (m := fun currentMotive _currentMotiveSuccessors motiveIH => by
      intro motiveChain currentZero currentSucc zeroChain succChain
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerZero =>
            StepStar zeroBranch innerZero →
            ∀ {laterSucc : RawTerm (scope + 2)},
              StepStar succBranch laterSucc →
              IsStronglyNormalizing (natRecCellSpine currentMotive scrutinee innerZero laterSucc))
          (m := fun currentInnerZero _currentInnerZeroSuccessors zeroIH => by
            intro innerZeroChain laterSucc laterSuccChain
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSucc =>
                  StepStar succBranch innerSucc →
                  IsStronglyNormalizing
                    (natRecCellSpine currentMotive scrutinee currentInnerZero innerSucc))
                (m := fun currentInnerSucc _currentInnerSuccSuccessors succIH => by
                  intro innerSuccChain
                  apply Acc.intro
                  intro target step
                  rcases Step.from_natRec step with
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

/-- **The `natElim` cell-SN theorem with a SATISFIABLE original-contractum-SN premise (the member-discharged
connector).**  Composes the reachability engine with the succ-iota contractum reduction-congruence: the engine's
`firingContractumSN` obligation at the stepped branches is discharged by `IsStronglyNormalizing.descendStepStar`
from the SN of the substituted succ-iota contractum at the ORIGINAL branches — `StepStar.natElimSuccContractumReduces`
carries the former to the latter as a reduct.  The remaining `originalContractumSN` premise (SN of the contractum
at the original branches, keyed on the firing equation `scrutinee = natSuccCell predecessor`) is exactly the CR1
shadow of the Tait member the value-reducibility arm already carries; unlike the engine's raw firing obligation it
quantifies over NO arbitrary currents, so it is the usable interface for the consumer rewire. -/
theorem natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (originalContractumSN :
      ∀ (predecessor : RawTerm scope), scrutinee = natSuccCell predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natElimCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)) :
    IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
  natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability
    scrutineeNormal motiveTerminates zeroBranchTerminates succBranchTerminates
    (fun _currentMotive _currentZero _currentSucc predecessor motiveChain zeroChain succChain scrutineeIsSucc =>
      IsStronglyNormalizing.descendStepStar
        (originalContractumSN predecessor scrutineeIsSucc)
        (natElimSuccContractumReduces motiveChain zeroChain succChain))

/-- **The `natRec` twin of the member-discharged connector.**  Same composition as the `natElim` connector with
`natRecCellSpine` and `StepStar.natRecSuccContractumReduces`. -/
theorem natRecCellSpine_isStronglyNormalizing_of_normalScrutinee_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (originalContractumSN :
      ∀ (predecessor : RawTerm scope), scrutinee = natSuccCell predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natRecCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)) :
    IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
  natRecCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability
    scrutineeNormal motiveTerminates zeroBranchTerminates succBranchTerminates
    (fun _currentMotive _currentZero _currentSucc predecessor motiveChain zeroChain succChain scrutineeIsSucc =>
      IsStronglyNormalizing.descendStepStar
        (originalContractumSN predecessor scrutineeIsSucc)
        (natRecSuccContractumReduces motiveChain zeroChain succChain))

/-- **The reduct-tracking `natElim` cell-SN engine for a REDUCING scrutinee (satisfiable firing premise).**  The
four-fold reachability generalization of `…_of_normalScrutinee_fromOriginalContractumSN`: the scrutinee need not
be normal — it is merely strongly normalizing — and the engine recurses on the scrutinee as well as the three
branches, threading a `StepStar` reachability witness through ALL FOUR `Acc.ndrec` levels.  The firing obligation
is replaced by the satisfiable `originalContractumSN`, keyed on the scrutinee REACHING a successor cell
(`StepStar scrutinee (natSuccCell predecessor)`): at the firing the scrutinee reachability identifies the
predecessor, the original contractum SN comes from `originalContractumSN`, and the stepped-branch contractum is
its reduct by `StepStar.natElimSuccContractumReduces` + `descendStepStar`.  This is the honest replacement for the
universally-false bare-SN firing premise of `natElim_isStronglyNormalizing_of_strongly_normalizing_branches` — the
scrutinee-reducing root the recursor value-reducibility consumers actually call. -/
theorem natElimCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (originalContractumSN :
      ∀ (predecessor : RawTerm scope), StepStar scrutinee (natSuccCell predecessor) →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natElimCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)) :
    IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      StepStar scrutinee currentScrutinee →
      ∀ {currentMotive : RawTerm (scope + 1)} {currentZero : RawTerm scope}
        {currentSucc : RawTerm (scope + 2)},
        StepStar motive currentMotive → StepStar zeroBranch currentZero →
        StepStar succBranch currentSucc →
        IsStronglyNormalizing (natElimCellSpine currentMotive currentScrutinee currentZero currentSucc))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro scrutineeReaches currentMotive currentZero currentSucc motiveReaches zeroReaches succReaches
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            StepStar motive innerMotive →
            ∀ {innerZero : RawTerm scope} {innerSucc : RawTerm (scope + 2)},
              StepStar zeroBranch innerZero → StepStar succBranch innerSucc →
              IsStronglyNormalizing (natElimCellSpine innerMotive currentScrutinee innerZero innerSucc))
          (m := fun currentInnerMotive _currentInnerMotiveSuccessors motiveIH => by
            intro motiveReaches' innerZero innerSucc zeroReaches' succReaches'
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerZeroVar =>
                  StepStar zeroBranch innerZeroVar →
                  ∀ {innerSuccVar : RawTerm (scope + 2)}, StepStar succBranch innerSuccVar →
                    IsStronglyNormalizing
                      (natElimCellSpine currentInnerMotive currentScrutinee innerZeroVar innerSuccVar))
                (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
                  intro zeroReaches'' innerSuccVar succReaches''
                  exact
                    (Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerSuccVar2 =>
                        StepStar succBranch innerSuccVar2 →
                        IsStronglyNormalizing
                          (natElimCellSpine currentInnerMotive currentScrutinee currentInnerZero innerSuccVar2))
                      (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
                        intro succReaches'''
                        apply Acc.intro
                        intro target step
                        rcases Step.from_natElim step with
                          ⟨_scrutineeIsZero, targetIsZero⟩ |
                          ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                          ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                          ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                          ⟨succAfter, targetIsSuccStep, succStep⟩ |
                          ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                        · rw [targetIsZero]
                          exact Acc.intro currentInnerZero currentInnerZeroSuccessors
                        · rw [targetIsContractum]
                          have scrutineeReachesSucc : StepStar scrutinee (natSuccCell predecessor) := by
                            rw [scrutineeIsSucc] at scrutineeReaches; exact scrutineeReaches
                          exact IsStronglyNormalizing.descendStepStar
                            (originalContractumSN predecessor scrutineeReachesSucc)
                            (natElimSuccContractumReduces motiveReaches' zeroReaches'' succReaches''')
                        · rw [targetIsMotiveStep]
                          exact motiveIH motiveAfter motiveStep
                            (StepStar.trans_compose motiveReaches' (StepStar.single motiveStep))
                            zeroReaches'' succReaches'''
                        · rw [targetIsZeroStep]
                          exact zeroIH zeroAfter zeroStep
                            (StepStar.trans_compose zeroReaches'' (StepStar.single zeroStep))
                            succReaches'''
                        · rw [targetIsSuccStep]
                          exact succIH succAfter succStep
                            (StepStar.trans_compose succReaches''' (StepStar.single succStep))
                        · rw [targetIsScrutineeStep]
                          exact scrutineeIH scrutineeAfter scrutineeStep
                            (StepStar.trans_compose scrutineeReaches (StepStar.single scrutineeStep))
                            motiveReaches' zeroReaches'' succReaches''')
                      (IsStronglyNormalizing.descendStepStar succBranchTerminates succReaches''))
                    succReaches'')
                (IsStronglyNormalizing.descendStepStar zeroBranchTerminates zeroReaches'))
              zeroReaches' succReaches')
          (IsStronglyNormalizing.descendStepStar motiveTerminates motiveReaches))
        motiveReaches zeroReaches succReaches)
    scrutineeTerminates)
    (StepStar.refl scrutinee) (StepStar.refl motive) (StepStar.refl zeroBranch) (StepStar.refl succBranch)

/-- **The reduct-tracking `natRec` cell-SN engine for a REDUCING scrutinee (satisfiable firing premise)** — the
`natRec` twin of `natElimCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN`.  Verbatim
mirror (swap `natElimCellSpine`→`natRecCellSpine`, `Step.from_natElim`→`Step.from_natRec`,
`natElimSuccContractumReduces`→`natRecSuccContractumReduces`); the recursors share the v2 substrate's arity-4
metadata, six-way inversion, and the 2-substituent succ-iota contractum shape. -/
theorem natRecCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (originalContractumSN :
      ∀ (predecessor : RawTerm scope), StepStar scrutinee (natSuccCell predecessor) →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natRecCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)) :
    IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      StepStar scrutinee currentScrutinee →
      ∀ {currentMotive : RawTerm (scope + 1)} {currentZero : RawTerm scope}
        {currentSucc : RawTerm (scope + 2)},
        StepStar motive currentMotive → StepStar zeroBranch currentZero →
        StepStar succBranch currentSucc →
        IsStronglyNormalizing (natRecCellSpine currentMotive currentScrutinee currentZero currentSucc))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro scrutineeReaches currentMotive currentZero currentSucc motiveReaches zeroReaches succReaches
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            StepStar motive innerMotive →
            ∀ {innerZero : RawTerm scope} {innerSucc : RawTerm (scope + 2)},
              StepStar zeroBranch innerZero → StepStar succBranch innerSucc →
              IsStronglyNormalizing (natRecCellSpine innerMotive currentScrutinee innerZero innerSucc))
          (m := fun currentInnerMotive _currentInnerMotiveSuccessors motiveIH => by
            intro motiveReaches' innerZero innerSucc zeroReaches' succReaches'
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerZeroVar =>
                  StepStar zeroBranch innerZeroVar →
                  ∀ {innerSuccVar : RawTerm (scope + 2)}, StepStar succBranch innerSuccVar →
                    IsStronglyNormalizing
                      (natRecCellSpine currentInnerMotive currentScrutinee innerZeroVar innerSuccVar))
                (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
                  intro zeroReaches'' innerSuccVar succReaches''
                  exact
                    (Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerSuccVar2 =>
                        StepStar succBranch innerSuccVar2 →
                        IsStronglyNormalizing
                          (natRecCellSpine currentInnerMotive currentScrutinee currentInnerZero innerSuccVar2))
                      (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
                        intro succReaches'''
                        apply Acc.intro
                        intro target step
                        rcases Step.from_natRec step with
                          ⟨_scrutineeIsZero, targetIsZero⟩ |
                          ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                          ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                          ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                          ⟨succAfter, targetIsSuccStep, succStep⟩ |
                          ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                        · rw [targetIsZero]
                          exact Acc.intro currentInnerZero currentInnerZeroSuccessors
                        · rw [targetIsContractum]
                          have scrutineeReachesSucc : StepStar scrutinee (natSuccCell predecessor) := by
                            rw [scrutineeIsSucc] at scrutineeReaches; exact scrutineeReaches
                          exact IsStronglyNormalizing.descendStepStar
                            (originalContractumSN predecessor scrutineeReachesSucc)
                            (natRecSuccContractumReduces motiveReaches' zeroReaches'' succReaches''')
                        · rw [targetIsMotiveStep]
                          exact motiveIH motiveAfter motiveStep
                            (StepStar.trans_compose motiveReaches' (StepStar.single motiveStep))
                            zeroReaches'' succReaches'''
                        · rw [targetIsZeroStep]
                          exact zeroIH zeroAfter zeroStep
                            (StepStar.trans_compose zeroReaches'' (StepStar.single zeroStep))
                            succReaches'''
                        · rw [targetIsSuccStep]
                          exact succIH succAfter succStep
                            (StepStar.trans_compose succReaches''' (StepStar.single succStep))
                        · rw [targetIsScrutineeStep]
                          exact scrutineeIH scrutineeAfter scrutineeStep
                            (StepStar.trans_compose scrutineeReaches (StepStar.single scrutineeStep))
                            motiveReaches' zeroReaches'' succReaches''')
                      (IsStronglyNormalizing.descendStepStar succBranchTerminates succReaches''))
                    succReaches'')
                (IsStronglyNormalizing.descendStepStar zeroBranchTerminates zeroReaches'))
              zeroReaches' succReaches')
          (IsStronglyNormalizing.descendStepStar motiveTerminates motiveReaches))
        motiveReaches zeroReaches succReaches)
    scrutineeTerminates)
    (StepStar.refl scrutinee) (StepStar.refl motive) (StepStar.refl zeroBranch) (StepStar.refl succBranch)

end StepStar
end FX1Poly.Core
