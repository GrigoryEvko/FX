import FX1Poly.Core.Eliminators.List.ListElimConsContractumReductionCongruence
import FX1Poly.Core.Metatheory.Canonicity.ListCanonicalFormsCandidate
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.ApplicationStrongNormalizationForward

/-! # FX1Poly/Core/ListElimReductTrackingStrongNormalization
    — the REDUCT-TRACKING `listElim` cell-SN engine + the member-discharged connector (the `listElim` twin of
      the nat recursor reduct-tracking engines)

The `listElim` analogue of the nat recursors' reachability-threaded cell-SN engine.  A `listElim` cell with a
NORMAL scrutinee and strongly-normalizing branches is strongly normalizing, given a firing obligation that
RECEIVES reachability witnesses (`StepStar motive currentMotive`, `StepStar nilBranch currentNil`, `StepStar
consBranch currentCons`) — making it SATISFIABLE: the cons-iota contractum at the stepped branches is a REDUCT
of the contractum at the originals (by `StepStar.listElimConsContractumReduces`), so its SN follows from the
original contractum's SN via `IsStronglyNormalizing.descendStepStar`.

Structurally a verbatim mirror of `natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability`:
three nested `Acc.ndrec` on `(motive, nilBranch, consBranch)`, scrutinee fixed normal, the six-way
`Step.from_listElim` inversion, each `Acc` motive carrying a leading `StepStar original current` hypothesis.  The
two genuine differences from nat: (1) the iota firing splits on `scrutinee = listConsCell head tail` (two
constructor components, not one predecessor), and (2) the cons-iota contractum is an APP-CHAIN
`app (app (app consBranch head) tail) (listElim motive nilBranch consBranch tail)`, not a substitution, so the
firing obligation's target is that app-chain and the discharge runs through `listElimConsContractumReduces` (the
app-chain congruence) rather than the nat `…SuccContractumReduces` (the substitution congruence).

The member-discharged connector `…_fromOriginalContractumSN` composes the engine with the congruence: the firing
obligation at the stepped branches is discharged by `descendStepStar` from the SN of the cons-iota contractum at
the ORIGINAL branches, leaving a satisfiable premise keyed on `scrutinee = listConsCell head tail` with no
arbitrary-current quantification — the CR1 shadow of the Tait member the value-reducibility arm already carries.

## Zero-axiom verification

`Acc.ndrec` / `Acc.intro` well-founded recursion, the pinned `Step.from_listElim` inversion,
`RawTerm.isStepNormalForm_blocks_step`, `IsStronglyNormalizing.descendStepStar`,
`StepStar.listElimConsContractumReduces`, and `StepStar.single` / `StepStar.trans_compose`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration swept by
`#audit_namespace FX1Poly.Core` in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
namespace StepStar

open FX1Poly.Tier0.Syntax

/-- **The reduct-tracking `listElim` cell-SN engine (satisfiable firing premise).**  A `listElim` cell with a
NORMAL scrutinee and strongly-normalizing branches is strongly normalizing, given the reachability-aware firing
obligation `firingContractumSN`: whenever the scrutinee is a cons cell `listConsCell head tail` and the current
branches are reachable from the originals, the cons-iota contractum app-chain at the current branches is strongly
normalizing.  The reachability witnesses make this dischargeable from the original contractum's SN via
`StepStar.listElimConsContractumReduces` + `descendStepStar`. -/
theorem listElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (nilBranchTerminates : IsStronglyNormalizing nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (firingContractumSN :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentNil currentCons head tail : RawTerm scope),
        StepStar motive currentMotive → StepStar nilBranch currentNil →
        StepStar consBranch currentCons → scrutinee = listConsCell head tail →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app () (.childCons currentCons (.childCons head .childNil)))
                  (.childCons tail .childNil)))
              (.childCons (listElimCellSpine currentMotive tail currentNil currentCons) .childNil)))) :
    IsStronglyNormalizing (listElimCellSpine motive scrutinee nilBranch consBranch) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun innerMotive =>
      StepStar motive innerMotive →
      ∀ {currentNil : RawTerm scope} {currentCons : RawTerm scope},
        StepStar nilBranch currentNil → StepStar consBranch currentCons →
        IsStronglyNormalizing (listElimCellSpine innerMotive scrutinee currentNil currentCons))
    (m := fun currentMotive _currentMotiveSuccessors motiveIH => by
      intro motiveChain currentNil currentCons nilChain consChain
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerNil =>
            StepStar nilBranch innerNil →
            ∀ {laterCons : RawTerm scope},
              StepStar consBranch laterCons →
              IsStronglyNormalizing (listElimCellSpine currentMotive scrutinee innerNil laterCons))
          (m := fun currentInnerNil _currentInnerNilSuccessors nilIH => by
            intro innerNilChain laterCons laterConsChain
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerCons =>
                  StepStar consBranch innerCons →
                  IsStronglyNormalizing
                    (listElimCellSpine currentMotive scrutinee currentInnerNil innerCons))
                (m := fun currentInnerCons _currentInnerConsSuccessors consIH => by
                  intro innerConsChain
                  apply Acc.intro
                  intro target step
                  rcases Step.from_listElim step with
                    ⟨_scrutineeIsNil, targetIsNil⟩ |
                    ⟨head, tail, scrutineeIsCons, targetIsContractum⟩ |
                    ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                    ⟨nilAfter, targetIsNilStep, nilStep⟩ |
                    ⟨consAfter, targetIsConsStep, consStep⟩ |
                    ⟨scrutineeAfter, _targetIsScrutineeStep, scrutineeStep⟩
                  · rw [targetIsNil]
                    exact IsStronglyNormalizing.descendStepStar nilBranchTerminates innerNilChain
                  · rw [targetIsContractum]
                    exact firingContractumSN currentMotive currentInnerNil currentInnerCons head tail
                      motiveChain innerNilChain innerConsChain scrutineeIsCons
                  · rw [targetIsMotiveStep]
                    exact motiveIH motiveAfter motiveStep
                      (StepStar.trans_compose motiveChain (StepStar.single motiveStep))
                      innerNilChain innerConsChain
                  · rw [targetIsNilStep]
                    exact nilIH nilAfter nilStep
                      (StepStar.trans_compose innerNilChain (StepStar.single nilStep))
                      innerConsChain
                  · rw [targetIsConsStep]
                    exact consIH consAfter consStep
                      (StepStar.trans_compose innerConsChain (StepStar.single consStep))
                  · exact absurd scrutineeStep
                      (RawTerm.isStepNormalForm_blocks_step scrutineeNormal scrutineeAfter))
                (IsStronglyNormalizing.descendStepStar consBranchTerminates laterConsChain))
              laterConsChain)
          (IsStronglyNormalizing.descendStepStar nilBranchTerminates nilChain))
        nilChain consChain)
    motiveTerminates)
    (StepStar.refl motive) (StepStar.refl nilBranch) (StepStar.refl consBranch)

/-- **The `listElim` cell-SN theorem with a SATISFIABLE original-contractum-SN premise (the member-discharged
connector).**  Composes the reachability engine with the cons-iota contractum reduction-congruence: the engine's
`firingContractumSN` obligation at the stepped branches is discharged by `IsStronglyNormalizing.descendStepStar`
from the SN of the cons-iota contractum app-chain at the ORIGINAL branches — `StepStar.listElimConsContractumReduces`
carries the former to the latter as a reduct.  The remaining `originalContractumSN` premise (keyed on
`scrutinee = listConsCell head tail`, NO arbitrary-current quantification) is the CR1 shadow of the Tait member
the value-reducibility arm already carries — the usable interface for the consumer rewire. -/
theorem listElimCellSpine_isStronglyNormalizing_of_normalScrutinee_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (nilBranchTerminates : IsStronglyNormalizing nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (originalContractumSN :
      ∀ (head tail : RawTerm scope), scrutinee = listConsCell head tail →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                  (.childCons tail .childNil)))
              (.childCons (listElimCellSpine motive tail nilBranch consBranch) .childNil)))) :
    IsStronglyNormalizing (listElimCellSpine motive scrutinee nilBranch consBranch) :=
  listElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability
    scrutineeNormal motiveTerminates nilBranchTerminates consBranchTerminates
    (fun _currentMotive _currentNil _currentCons head tail motiveChain nilChain consChain scrutineeIsCons =>
      IsStronglyNormalizing.descendStepStar
        (originalContractumSN head tail scrutineeIsCons)
        (listElimConsContractumReduces motiveChain nilChain consChain))

/-- **The reduct-tracking `listElim` cell-SN engine for a REDUCING scrutinee (satisfiable firing premise)** — the
`listElim` twin of the four-fold nat scrutinee-reducing engines.  Four-fold `Acc.ndrec` on
(scrutinee, motive, nilBranch, consBranch) threading a `StepStar` reachability witness through every level; the
scrutinee need not be normal.  The firing obligation is the satisfiable `originalContractumSN`, keyed on the
scrutinee REACHING a cons cell (`StepStar scrutinee (listConsCell head tail)`): at the cons-iota the scrutinee
reachability identifies head/tail, the original app-chain contractum SN comes from `originalContractumSN`, and the
stepped-branch contractum is its reduct by `StepStar.listElimConsContractumReduces` + `descendStepStar`.  The
honest replacement for the false bare-SN firing premise of the scrutinee-reducing `listElim` SN root. -/
theorem listElimCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (nilBranchTerminates : IsStronglyNormalizing nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (originalContractumSN :
      ∀ (head tail : RawTerm scope), StepStar scrutinee (listConsCell head tail) →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                  (.childCons tail .childNil)))
              (.childCons (listElimCellSpine motive tail nilBranch consBranch) .childNil)))) :
    IsStronglyNormalizing (listElimCellSpine motive scrutinee nilBranch consBranch) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      StepStar scrutinee currentScrutinee →
      ∀ {currentMotive : RawTerm (scope + 1)} {currentNil : RawTerm scope} {currentCons : RawTerm scope},
        StepStar motive currentMotive → StepStar nilBranch currentNil →
        StepStar consBranch currentCons →
        IsStronglyNormalizing (listElimCellSpine currentMotive currentScrutinee currentNil currentCons))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro scrutineeReaches currentMotive currentNil currentCons motiveReaches nilReaches consReaches
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            StepStar motive innerMotive →
            ∀ {innerNil : RawTerm scope} {innerCons : RawTerm scope},
              StepStar nilBranch innerNil → StepStar consBranch innerCons →
              IsStronglyNormalizing (listElimCellSpine innerMotive currentScrutinee innerNil innerCons))
          (m := fun currentInnerMotive _currentInnerMotiveSuccessors motiveIH => by
            intro motiveReaches' innerNil innerCons nilReaches' consReaches'
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerNilVar =>
                  StepStar nilBranch innerNilVar →
                  ∀ {innerConsVar : RawTerm scope}, StepStar consBranch innerConsVar →
                    IsStronglyNormalizing
                      (listElimCellSpine currentInnerMotive currentScrutinee innerNilVar innerConsVar))
                (m := fun currentInnerNil currentInnerNilSuccessors nilIH => by
                  intro nilReaches'' innerConsVar consReaches''
                  exact
                    (Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerConsVar2 =>
                        StepStar consBranch innerConsVar2 →
                        IsStronglyNormalizing
                          (listElimCellSpine currentInnerMotive currentScrutinee currentInnerNil innerConsVar2))
                      (m := fun currentInnerCons currentInnerConsSuccessors consIH => by
                        intro consReaches'''
                        apply Acc.intro
                        intro target step
                        rcases Step.from_listElim step with
                          ⟨_scrutineeIsNil, targetIsNil⟩ |
                          ⟨head, tail, scrutineeIsCons, targetIsContractum⟩ |
                          ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                          ⟨nilAfter, targetIsNilStep, nilStep⟩ |
                          ⟨consAfter, targetIsConsStep, consStep⟩ |
                          ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                        · rw [targetIsNil]
                          exact Acc.intro currentInnerNil currentInnerNilSuccessors
                        · rw [targetIsContractum]
                          have scrutineeReachesCons : StepStar scrutinee (listConsCell head tail) := by
                            rw [scrutineeIsCons] at scrutineeReaches; exact scrutineeReaches
                          exact IsStronglyNormalizing.descendStepStar
                            (originalContractumSN head tail scrutineeReachesCons)
                            (listElimConsContractumReduces motiveReaches' nilReaches'' consReaches''')
                        · rw [targetIsMotiveStep]
                          exact motiveIH motiveAfter motiveStep
                            (StepStar.trans_compose motiveReaches' (StepStar.single motiveStep))
                            nilReaches'' consReaches'''
                        · rw [targetIsNilStep]
                          exact nilIH nilAfter nilStep
                            (StepStar.trans_compose nilReaches'' (StepStar.single nilStep))
                            consReaches'''
                        · rw [targetIsConsStep]
                          exact consIH consAfter consStep
                            (StepStar.trans_compose consReaches''' (StepStar.single consStep))
                        · rw [targetIsScrutineeStep]
                          exact scrutineeIH scrutineeAfter scrutineeStep
                            (StepStar.trans_compose scrutineeReaches (StepStar.single scrutineeStep))
                            motiveReaches' nilReaches'' consReaches''')
                      (IsStronglyNormalizing.descendStepStar consBranchTerminates consReaches''))
                    consReaches'')
                (IsStronglyNormalizing.descendStepStar nilBranchTerminates nilReaches'))
              nilReaches' consReaches')
          (IsStronglyNormalizing.descendStepStar motiveTerminates motiveReaches))
        motiveReaches nilReaches consReaches)
    scrutineeTerminates)
    (StepStar.refl scrutinee) (StepStar.refl motive) (StepStar.refl nilBranch) (StepStar.refl consBranch)

end StepStar
end FX1Poly.Core
