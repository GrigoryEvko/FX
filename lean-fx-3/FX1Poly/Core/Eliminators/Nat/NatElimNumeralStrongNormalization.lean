import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationNatElim
import FX1Poly.Core.Metatheory.Canonicity.NatCanonicalFormsCandidate
import FX1Poly.Core.Rewriting.Normalize.RawTermNF

/-! # FX1Poly/Core/NatElimNumeralStrongNormalization
    — the RESIDUE-FREE recursor cell-SN engine: `natElim` SN for a NORMAL scrutinee (the FTGEN-13.1 keystone core)

`StrongNormalizationNatElim.natElim_isStronglyNormalizing_of_strongly_normalizing_branches` proves the `natElim`
cell strongly normalizing from SN branches, but it threads the OVER-GENERAL residue

```
succContractumTerminates :
  ∀ currentMotive currentSucc predecessor currentZero, IsStronglyNormalizing predecessor →
    IsStronglyNormalizing (succ-ι contractum)
```

— a hypothesis quantified over EVERY strongly-normalizing predecessor.  That residue is unsatisfiable at the open
level: the contractum embeds the recursive `natElimCellSpine currentMotive predecessor …` at an arbitrary SN
predecessor, and raw recursors are not globally SN.  It is the single obstruction standing between the per-row
bounded fundamental theorem and the consistency leg's bare `elimFundamental` premise (the recursor-SN keystone).

This file ships the engine that REPLACES that residue with a far weaker, dischargeable obligation.  For a scrutinee
that is a NORMAL FORM, the cell can only step by congruence into a branch or by an ι-firing — there is NO
scrutinee-congruence (the scrutinee is already normal).  So the cell SN needs the contractum SN ONLY at the single
predecessor the ι actually fires on, i.e. only when `scrutinee = natSuccCell predecessor`.  The premise

```
succContractumSN :
  ∀ currentMotive currentZero currentSucc predecessor, … → scrutinee = natSuccCell predecessor →
    IsStronglyNormalizing (succ-ι contractum)
```

is conditioned on the firing actually happening for THIS scrutinee — a single obligation, not a universal over all
predecessors.  When the scrutinee is a numeral `natSuccCell pred`, that obligation is discharged by the structural
numeral induction: the recursive call `natElimCellSpine currentMotive pred …` is SN by the inductive hypothesis
(pred is structurally smaller), and the branch's substitution-closure lands the contractum.  That numeral-induction
wrapper is the next brick; this file is its load-bearing core.

## The proof

A three-fold nested `Acc.ndrec` on the branches `(motive, zeroBranch, succBranch)`, mirroring the inner three
folds of `natElim_isStronglyNormalizing_of_strongly_normalizing_branches` but DROPPING the scrutinee fold (the
scrutinee is fixed and normal) and DROPPING the residue threading (the firing obligation `succContractumSN` and
the normality fact `scrutineeNormal` are ambient).  The pinned six-way `Step.from_natElim` splits the arms:
ι-zero → the current zero branch (SN from its accessibility); ι-succ → the contractum, discharged by
`succContractumSN` at the firing predecessor; the three branch-congruences → the corresponding inductive
hypotheses; scrutinee-congruence → impossible by `RawTerm.isStepNormalForm_blocks_step` on the normal scrutinee.

## Zero-axiom verification

`Acc.ndrec` / `Acc.intro` well-founded recursion, the pinned `Step.from_natElim` inversion, and
`RawTerm.isStepNormalForm_blocks_step`.  No induction-recursion, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- **★ The residue-free recursor cell-SN engine.**  A `natElim` cell with a NORMAL scrutinee and
strongly-normalizing branches is strongly normalizing, given the contractum is strongly normalizing whenever the
scrutinee is a successor (`succContractumSN`).  Unlike
`natElim_isStronglyNormalizing_of_strongly_normalizing_branches`, the firing obligation is conditioned on the
scrutinee actually being `natSuccCell predecessor` — a single firing, not the over-general
`∀ predecessor, IsStronglyNormalizing predecessor → …` residue that is unsatisfiable for open terms.  A three-fold
`Acc.ndrec` on `(motive, zeroBranch, succBranch)`: scrutinee-congruence is impossible (the scrutinee is normal),
ι-zero lands on the current zero branch, ι-succ on the contractum (`succContractumSN`), and the three branch
congruences recurse.  The keystone core that the numeral-induction wrapper closes (the recursive call's SN comes
from the structural numeral IH, discharging `succContractumSN`). -/
theorem natElimCellSpine_isStronglyNormalizing_of_normalScrutinee {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succContractumSN :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope),
        IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
        IsStronglyNormalizing currentSucc →
        scrutinee = natSuccCell predecessor →
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
      ∀ {currentZero : RawTerm scope} {currentSucc : RawTerm (scope + 2)},
        IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
        IsStronglyNormalizing (natElimCellSpine innerMotive scrutinee currentZero currentSucc))
    (m := fun currentMotive currentMotiveSuccessors motiveIH => by
      intro currentZero currentSucc currentZeroTerminates currentSuccTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerZero =>
            ∀ {laterSucc : RawTerm (scope + 2)},
              IsStronglyNormalizing laterSucc →
              IsStronglyNormalizing (natElimCellSpine currentMotive scrutinee innerZero laterSucc))
          (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
            intro laterSucc laterSuccTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSucc =>
                  IsStronglyNormalizing
                    (natElimCellSpine currentMotive scrutinee currentInnerZero innerSucc))
                (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
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
                    exact Acc.intro currentInnerZero currentInnerZeroSuccessors
                  · rw [targetIsContractum]
                    exact succContractumSN currentMotive currentInnerZero currentInnerSucc
                      predecessor
                      (Acc.intro currentMotive currentMotiveSuccessors)
                      (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                      (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                      scrutineeIsSucc
                  · rw [targetIsMotiveStep]
                    exact motiveIH motiveAfter motiveStep
                      (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                      (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                  · rw [targetIsZeroStep]
                    exact zeroIH zeroAfter zeroStep
                      (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                  · rw [targetIsSuccStep]
                    exact succIH succAfter succStep
                  · exact absurd scrutineeStep
                      (RawTerm.isStepNormalForm_blocks_step scrutineeNormal scrutineeAfter))
                laterSuccTerminates)
          currentZeroTerminates)
          currentSuccTerminates)
    motiveTerminates)
    zeroBranchTerminates succBranchTerminates

end StepStar
end FX1Poly.Core
