import FX1Poly.Core.Eliminators.Nat.NatElimNumeralStrongNormalization
import FX1Poly.Core.Metatheory.Canonicity.NatStructuredCandidate

/-! # FX1Poly/Core/NatElimStructuredMemberStrongNormalization
    — the RESIDUE-FREE recursor cell-SN inner engine: `natElim` SN from a STRUCTURED-MEMBER scrutinee
    (the FTGEN-13.1 membership-combine heart that refutes the `succContractumTerminates` residue)

`natElimCellSpine_isStronglyNormalizing_of_normalScrutinee` (the numeral engine) handles a scrutinee that is
already a NORMAL form: the cell can only step into a branch or fire its ι, never reduce the (already normal)
scrutinee.  For a scrutinee that is merely a MEMBER of the structured Nat candidate
(`dataTaitCandidate IsNatStructured`) — strongly normalizing, reducing to a structured value, but NOT itself a
normal form — the cell additionally has SCRUTINEE-CONGRUENCE reducts: every reduct of the scrutinee yields a
reduct of the cell.  Worse, the scrutinee may be `natSucc`-headed BEFORE it is normal (`natSucc redex`), so the
ι can fire at an intermediate, non-normal predecessor.

This file ships the engine that handles BOTH: a four-fold `Acc StepSuccessor` over the scrutinee and the three
branches.  The scrutinee fold is OUTERMOST; its inductive hypothesis discharges the scrutinee-congruence arm (the
stepped scrutinee is still a member by CR2, and still reaches the same structured value by confluence —
`stepStar_focus_reaches_normal_target`).  The three branch folds are nested inside, exactly as in the numeral
engine.  The ι-succ firing — at a possibly-intermediate `natSucc predecessor` — is discharged by a CALLBACK
`succFiringDischarge` conditioned on the scrutinee reaching the (normal) structured target; the membership-combine
that wraps this engine supplies that callback from the OUTER structural induction on `IsNatStructured` (the
predecessor reaches a structurally-smaller value, so its recursive cell SN is the structural IH — never the
over-general `succContractumTerminates` residue, which quantifies over arbitrary strongly-normalizing predecessors
and is unsatisfiable for open terms).

## The four-fold accessibility

`Acc.ndrec` on the scrutinee carrying the membership and the reaches-target witness in its motive (so the
scrutinee-congruence recursion can re-thread them), with the three branch folds nested in its body.  The six-way
`Step.from_natElim` splits the cell's reducts: ι-zero → the current zero branch; ι-succ → `succFiringDischarge`;
the three branch congruences → the corresponding branch inductive hypotheses; scrutinee-congruence → the scrutinee
inductive hypothesis at the stepped (still-member, still-reaching) scrutinee.

## Zero-axiom verification

`Acc.ndrec` / `Acc.intro` well-founded recursion, the pinned `Step.from_natElim` inversion,
`stepStar_focus_reaches_normal_target` (per-term confluence on the SN member), and the structured-candidate CR2
(`dataTaitCandidate.closedUnderStep`).  No induction-recursion, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- **★ The residue-free recursor cell-SN inner engine for a structured-member scrutinee.**  A `natElim` cell
whose scrutinee is a member of the structured Nat candidate (`dataTaitCandidate IsNatStructured`), reaches a
NORMAL structured target, and has strongly-normalizing branches, is strongly normalizing — given the ι-succ
firing obligation `succFiringDischarge` (the substituted succ-contractum is SN whenever the scrutinee is a
`natSuccCell predecessor` reaching the target).  Unlike the over-general `succContractumTerminates` residue,
`succFiringDischarge` is conditioned on the scrutinee reaching the structured target, so the membership-combine
discharges it per structural layer from the outer `IsNatStructured` induction (the predecessor reaches a smaller
value).  A four-fold `Acc StepSuccessor` (scrutinee outermost, then the three branches): scrutinee-congruence
recurses via the scrutinee IH (CR2 keeps the reduct a member; confluence keeps it reaching the normal target),
ι-zero lands on the current zero branch, ι-succ on `succFiringDischarge`, the three branch congruences recurse.
The branches are quantified in the scrutinee fold's motive so the scrutinee IH applies at the current (possibly
branch-stepped) branches. -/
theorem natElimCellSpine_isStronglyNormalizing_of_structuredMemberReaching {scope : Nat}
    {structuredTarget : RawTerm scope}
    (structuredTargetIsNormal : RawTerm.isStepNormalForm structuredTarget)
    (succFiringDischarge :
      ∀ {currentScrutinee predecessor : RawTerm scope},
        dataTaitCandidate IsNatStructured currentScrutinee →
        StepStar currentScrutinee structuredTarget →
        currentScrutinee = natSuccCell predecessor →
        ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
          (currentSucc : RawTerm (scope + 2)),
          IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
          IsStronglyNormalizing currentSucc →
          IsStronglyNormalizing
            (RawTerm.subst
              (RawTermSubst.cons
                (natElimCellSpine currentMotive predecessor currentZero currentSucc)
                (RawTermSubst.singleton predecessor))
              currentSucc)) :
    ∀ {scrutinee : RawTerm scope},
      dataTaitCandidate IsNatStructured scrutinee →
      StepStar scrutinee structuredTarget →
      ∀ {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)},
        IsStronglyNormalizing motive → IsStronglyNormalizing zeroBranch → IsStronglyNormalizing succBranch →
        IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) := by
  intro scrutinee scrutineeMember
  -- Outermost fold: accessibility of the scrutinee, carrying the membership + reaches-target witness so the
  -- scrutinee-congruence arm can re-thread them onto the stepped reduct.
  refine
    (Acc.ndrec
      (r := StepSuccessor)
      (C := fun innerScrutinee =>
        dataTaitCandidate IsNatStructured innerScrutinee →
        StepStar innerScrutinee structuredTarget →
        ∀ {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)},
          IsStronglyNormalizing motive → IsStronglyNormalizing zeroBranch → IsStronglyNormalizing succBranch →
          IsStronglyNormalizing (natElimCellSpine motive innerScrutinee zeroBranch succBranch))
      (m := fun currentScrutinee _currentScrutineeSuccessors scrutineeIH => by
        intro currentMember currentReaches motive zeroBranch succBranch
          motiveTerminates zeroBranchTerminates succBranchTerminates
        -- Three nested branch folds, exactly as in the numeral engine.
        exact
          (Acc.ndrec
            (r := StepSuccessor)
            (C := fun innerMotive =>
              ∀ {currentZero : RawTerm scope} {currentSucc : RawTerm (scope + 2)},
                IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
                IsStronglyNormalizing (natElimCellSpine innerMotive currentScrutinee currentZero currentSucc))
            (m := fun currentMotive currentMotiveSuccessors motiveIH => by
              intro currentZero currentSucc currentZeroTerminates currentSuccTerminates
              exact
                (Acc.ndrec
                  (r := StepSuccessor)
                  (C := fun innerZero =>
                    ∀ {laterSucc : RawTerm (scope + 2)},
                      IsStronglyNormalizing laterSucc →
                      IsStronglyNormalizing (natElimCellSpine currentMotive currentScrutinee innerZero laterSucc))
                  (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
                    intro laterSucc laterSuccTerminates
                    exact
                      Acc.ndrec
                        (r := StepSuccessor)
                        (C := fun innerSucc =>
                          IsStronglyNormalizing
                            (natElimCellSpine currentMotive currentScrutinee currentInnerZero innerSucc))
                        (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
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
                            exact succFiringDischarge currentMember currentReaches scrutineeIsSucc
                              currentMotive currentInnerZero currentInnerSucc
                              (Acc.intro currentMotive currentMotiveSuccessors)
                              (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                              (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                          · rw [targetIsMotiveStep]
                            exact motiveIH motiveAfter motiveStep
                              (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                              (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                          · rw [targetIsZeroStep]
                            exact zeroIH zeroAfter zeroStep
                              (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                          · rw [targetIsSuccStep]
                            exact succIH succAfter succStep
                          · rw [targetIsScrutineeStep]
                            exact scrutineeIH scrutineeAfter scrutineeStep
                              (currentMember.closedUnderStep scrutineeStep)
                              (stepStar_focus_reaches_normal_target currentMember.1
                                (StepStar.single scrutineeStep) currentReaches structuredTargetIsNormal)
                              (Acc.intro currentMotive currentMotiveSuccessors)
                              (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                              (Acc.intro currentInnerSucc currentInnerSuccSuccessors))
                        laterSuccTerminates)
                  currentZeroTerminates)
                  currentSuccTerminates)
            motiveTerminates)
            zeroBranchTerminates succBranchTerminates)
      scrutineeMember.1)
    scrutineeMember

/-- **★ The residue-free membership-based recursor cell SN (FTGEN-13.1 — the #1697 elim unlock).**  A `natElim`
cell whose scrutinee is a member of the structured Nat candidate (`dataTaitCandidate IsNatStructured`) and whose
branches are strongly normalizing is strongly normalizing — WITHOUT the over-general `succContractumTerminates`
residue.  The structural induction on the structured value the scrutinee reaches
(`natStructuredMemberReachesStructuredValue`) supplies the inner engine's ι-succ firing obligation: at the `succ`
node, the firing predecessor reaches the structurally-SMALLER value, so the recursive cell SN is the OUTER
inductive hypothesis (`outerInductiveHypothesis` at the predecessor) landed by `succBranchSubstClosed` — never the
unsatisfiable residue; at the `zero` and `neutralNormal` leaves the firing is vacuous (a `natSuccCell` never
reaches `natZero` or a neutral, by `stepStar_under_unaryCell` + the head discriminators).  The branches are
quantified in the inductive conclusion so the outer hypothesis applies at the recursive call's (possibly stepped)
branches.

This refutes the firing-#18 caveat: the bare elim-fundamental premise hands the scrutinee-obligation IH (hence the
scrutinee MEMBERSHIP), and the ι-succ predecessor is then a member reaching a smaller value, NOT an arbitrary
strongly-normalizing term — so `succContractumTerminates` IS dischargeable.  `succBranchSubstClosed` is the genuine
fundamental-theorem-of-the-branch content (a member predecessor and a member recursive result land the substituted
contractum SN), carrying no recursion. -/
theorem natElimCellSpine_isStronglyNormalizing_of_structuredMember {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchSubstClosed :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor recursiveResult : RawTerm scope),
        IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
        IsStronglyNormalizing currentSucc → dataTaitCandidate IsNatStructured predecessor →
        IsStronglyNormalizing recursiveResult →
        IsStronglyNormalizing
          (RawTerm.subst (RawTermSubst.cons recursiveResult (RawTermSubst.singleton predecessor))
            currentSucc))
    (scrutineeMember : dataTaitCandidate IsNatStructured scrutinee) :
    IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) := by
  obtain ⟨structuredValue, scrutineeReachesValue, structuredValueIsStructured⟩ :=
    natStructuredMemberReachesStructuredValue scrutineeMember
  suffices aux : ∀ {structured : RawTerm scope}, IsNatStructured structured →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsNatStructured currentScrutinee →
        StepStar currentScrutinee structured →
        ∀ {currentMotive : RawTerm (scope + 1)} {currentZero : RawTerm scope}
          {currentSucc : RawTerm (scope + 2)},
          IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
          IsStronglyNormalizing currentSucc →
          IsStronglyNormalizing (natElimCellSpine currentMotive currentScrutinee currentZero currentSucc) from
    aux structuredValueIsStructured scrutineeMember scrutineeReachesValue
      motiveTerminates zeroBranchTerminates succBranchTerminates
  intro structured structuredIsStructured
  induction structuredIsStructured with
  | zero =>
      refine natElimCellSpine_isStronglyNormalizing_of_structuredMemberReaching
        (isNatStructured_impliesStepNormalForm IsNatStructured.zero) ?_
      intro currentScrutinee predecessor currentMember currentReaches currentEquation
        _currentMotive _currentZero _currentSucc _ _ _
      have reachesZero : StepStar (natSuccCell predecessor) natZeroCell := currentEquation ▸ currentReaches
      obtain ⟨_predecessorAfter, zeroEqualsSucc, _⟩ :=
        stepStar_under_unaryCell natSuccCell Step.from_natSucc reachesZero predecessor rfl
      exact Generator.noConfusion (congrArg RawTerm.rootGenerator zeroEqualsSucc)
  | @neutralNormal neutralTerm neutralTermIsNeutral neutralTermIsNormal =>
      refine natElimCellSpine_isStronglyNormalizing_of_structuredMemberReaching
        neutralTermIsNormal ?_
      intro currentScrutinee predecessor currentMember currentReaches currentEquation
        _currentMotive _currentZero _currentSucc _ _ _
      have reachesNeutral : StepStar (natSuccCell predecessor) neutralTerm := currentEquation ▸ currentReaches
      obtain ⟨_predecessorAfter, neutralEqualsSucc, _⟩ :=
        stepStar_under_unaryCell natSuccCell Step.from_natSucc reachesNeutral predecessor rfl
      exact (isNeutral_rootGenerator_ne_natSucc (neutralEqualsSucc ▸ neutralTermIsNeutral) rfl).elim
  | @succ valuePredecessor valuePredecessorIsStructured outerInductiveHypothesis =>
      refine natElimCellSpine_isStronglyNormalizing_of_structuredMemberReaching
        (isNatStructured_impliesStepNormalForm (IsNatStructured.succ valuePredecessorIsStructured)) ?_
      intro currentScrutinee predecessor currentMember currentReaches currentEquation
        currentMotive currentZero currentSucc currentMotiveSN currentZeroSN currentSuccSN
      have reachesSucc : StepStar (natSuccCell predecessor) (natSuccCell valuePredecessor) :=
        currentEquation ▸ currentReaches
      obtain ⟨predecessorAfter, succEquation, predecessorReachesAfter⟩ :=
        stepStar_under_unaryCell natSuccCell Step.from_natSucc reachesSucc predecessor rfl
      have predecessorAfterEqualsValue : predecessorAfter = valuePredecessor :=
        (natSuccCell_inj succEquation).symm
      subst predecessorAfterEqualsValue
      have predecessorMember : dataTaitCandidate IsNatStructured predecessor :=
        natSuccStructuredMember_predecessor (currentEquation ▸ currentMember)
      have recursiveCellSN :
          IsStronglyNormalizing (natElimCellSpine currentMotive predecessor currentZero currentSucc) :=
        outerInductiveHypothesis predecessorMember predecessorReachesAfter
          currentMotiveSN currentZeroSN currentSuccSN
      exact succBranchSubstClosed currentMotive currentZero currentSucc predecessor
        (natElimCellSpine currentMotive predecessor currentZero currentSucc)
        currentMotiveSN currentZeroSN currentSuccSN predecessorMember recursiveCellSN

end StepStar
end FX1Poly.Core
