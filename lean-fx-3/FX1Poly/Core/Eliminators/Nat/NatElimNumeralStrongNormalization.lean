import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationNatElim
import FX1Poly.Core.Metatheory.Canonicity.NatCanonicalFormsCandidate
import FX1Poly.Core.Rewriting.Normalize.RawTermNF
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibilityCandidateArrow

/-! # FX1Poly/Core/NatElimNumeralStrongNormalization
    — the recursor cell-SN engine for a NORMAL scrutinee: reduces cell SN to the single firing contractum
      (an FTGEN-13.1 building block, NOT the closure — see the honest caveat on the numeral wrapper below)

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

This file ships the engine that REDUCES that residue to a single firing obligation — but does NOT discharge it
(the discharge needs Tait membership; see the honest caveat on the numeral wrapper).  For a scrutinee
that is a NORMAL FORM, the cell can only step by congruence into a branch or by an ι-firing — there is NO
scrutinee-congruence (the scrutinee is already normal).  So the cell SN needs the contractum SN ONLY at the single
predecessor the ι actually fires on, i.e. only when `scrutinee = natSuccCell predecessor`.  The premise

```
succContractumSN :
  ∀ currentMotive currentZero currentSucc predecessor, … → scrutinee = natSuccCell predecessor →
    IsStronglyNormalizing (succ-ι contractum)
```

is conditioned on the firing actually happening for THIS scrutinee — a single obligation, not a universal over all
predecessors.  When the scrutinee is a numeral `natSuccCell pred`, the structural numeral induction REDUCES that
firing obligation to a branch substitution-closure premise (`succBranchSubstClosed`): the recursive call
`natElimCellSpine currentMotive pred …` is SN by the inductive hypothesis (pred is structurally smaller), and the
substitution-closure must land the contractum.  HONEST CAVEAT: that `succBranchSubstClosed` premise is NOT itself
discharged here — it RELOCATES the false residue rather than eliminating it (it is universally false at open scope:
see the numeral wrapper's counterexample), so this file does NOT close FTGEN-13.1.  The genuine residue-free
discharge threads Tait MEMBERSHIP (CR2 + a uniform member-branch closure), which is the open #1754 work.

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

/-- **The recursor cell-SN engine for a NORMAL scrutinee (firing-reduced, not residue-free).**  A `natElim` cell
with a NORMAL scrutinee and strongly-normalizing branches is strongly normalizing, given the contractum is strongly
normalizing whenever the scrutinee is a successor (`succContractumSN`).  This is a sound conditional that REDUCES the
cell-SN obligation to the single firing contractum; it does NOT discharge that contractum (see the numeral wrapper's
honest caveat — the discharge needs Tait membership, not bare SN).  Unlike
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

/-- **`natSucc` is injective.**  Two `natSuccCell` cells over equal predecessors are equal terms iff their
predecessors are equal — the constructor injectivity for `gen_natSucc`'s single child.  Mirrors
`pathLamValueCell_inj`: the `mkGen` injection exposes the children equality, then `RawTermChildren.childCons.inj`
projects the head (the indices coincide, so the injection emits a plain `Eq` head component).  Used by the
numeral wrapper to identify the `Step.from_natElim` successor witness with the structural predecessor. -/
theorem natSuccCell_inj {scope : Nat} {first second : RawTerm scope}
    (equal : natSuccCell first = natSuccCell second) : first = second := by
  injection equal with _scopeEq _generatorEq _payloadEq childrenEq
  exact (RawTermChildren.childCons.inj childrenEq).1

/-- **The recursor cell-SN for a NUMERAL scrutinee, modulo the substitution-closure residue (NOT FTGEN-13.1).**
A `natElim` cell whose scrutinee is a numeral (`IsNatValue`) and whose branches are strongly normalizing is
strongly normalizing — GIVEN `succBranchSubstClosed`.  Induction on the numeral feeds the engine's single firing
obligation: a numeral is a normal form (`isNatValue_impliesStepNormalForm`), so
`natElimCellSpine_isStronglyNormalizing_of_normalScrutinee` reduces cell SN to the contractum SN at the firing
predecessor; at `natSuccCell pred` the recursive call `natElimCellSpine currentMotive pred …` is strongly
normalizing by the structural inductive hypothesis (`pred` smaller, the IH universal over the branches), and
`succBranchSubstClosed` is asked to land the substituted contractum.
**HONEST CAVEAT (corrects an earlier "residue-free / FTGEN-13.1 closed" overclaim):** this RELOCATES the residue
rather than eliminating it.  `succBranchSubstClosed` — SN of the succ-branch substituted with an ARBITRARY SN
recursive result and a value predecessor — is itself UNIVERSALLY FALSE at open scope, by the same
substitution-does-not-preserve-SN counterexample that refutes `succContractumTerminates`:
`currentSucc := app (var 0) (var 0)` (a normal form, hence SN), `recursiveResult := lam (app (var 0) (var 0))`
(a value, hence SN) give the substituted contractum `(lam x. x x) (lam x. x x) = Ω`, which is NOT SN.  A bare-SN
recursive result cannot land the contractum.  The genuine residue-free discharge (FTGEN-13.1 #1754) must thread
Tait MEMBERSHIP: CR2 (`CanonicalFormsPredicate.closedUnderStep`) to keep the engine's STEPPED branches members,
plus a uniform member-branch contractum closure (member recursive result ⟹ member contractum) — which requires the
SN engine to carry membership, not just SN, through its `Acc` recursion.  This lemma is a sound implication and a
load-bearing building block, but it does NOT by itself close the recursor-SN keystone.
The successor witness from `Step.from_natElim` is identified with the structural `pred` by `natSuccCell_inj`; the
zero case's firing obligation is vacuous (`natZeroCell ≠ natSuccCell _`). -/
theorem natElimCellSpine_isStronglyNormalizing_of_natValueScrutinee {scope : Nat}
    {scrutinee : RawTerm scope}
    (scrutineeIsNatValue : IsNatValue scrutinee)
    (succBranchSubstClosed :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor recursiveResult : RawTerm scope),
        IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
        IsStronglyNormalizing currentSucc → IsNatValue predecessor →
        IsStronglyNormalizing recursiveResult →
        IsStronglyNormalizing
          (RawTerm.subst (RawTermSubst.cons recursiveResult (RawTermSubst.singleton predecessor))
            currentSucc)) :
    ∀ {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)},
      IsStronglyNormalizing motive → IsStronglyNormalizing zeroBranch → IsStronglyNormalizing succBranch →
      IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) := by
  induction scrutineeIsNatValue with
  | zero =>
      intro motive zeroBranch succBranch motiveTerminates zeroBranchTerminates succBranchTerminates
      exact natElimCellSpine_isStronglyNormalizing_of_normalScrutinee
        (isNatValue_impliesStepNormalForm IsNatValue.zero)
        motiveTerminates zeroBranchTerminates succBranchTerminates
        (fun _currentMotive _currentZero _currentSucc _predecessor _ _ _ scrutineeIsSucc =>
          Generator.noConfusion
            (congrArg RawTerm.rootGenerator scrutineeIsSucc :
              Generator.gen_natZero = Generator.gen_natSucc))
  | @succ pred predIsNatValue predIH =>
      intro motive zeroBranch succBranch motiveTerminates zeroBranchTerminates succBranchTerminates
      refine natElimCellSpine_isStronglyNormalizing_of_normalScrutinee
        (isNatValue_impliesStepNormalForm (IsNatValue.succ predIsNatValue))
        motiveTerminates zeroBranchTerminates succBranchTerminates
        (fun currentMotive currentZero currentSucc predecessor currentMotiveSN currentZeroSN
            currentSuccSN scrutineeIsSucc => ?_)
      have predEq : pred = predecessor := natSuccCell_inj scrutineeIsSucc
      subst predEq
      exact succBranchSubstClosed currentMotive currentZero currentSucc pred
        (natElimCellSpine currentMotive pred currentZero currentSucc)
        currentMotiveSN currentZeroSN currentSuccSN predIsNatValue
        (predIH currentMotiveSN currentZeroSN currentSuccSN)

/-- **The recursor cell-SN engine for a NORMAL scrutinee — the `natRec` twin.**  Identical to
`natElimCellSpine_isStronglyNormalizing_of_normalScrutinee` for the `gen_natRec` generator: `gen_natElim` and
`gen_natRec` share the v2 substrate's metadata (same arity-4 motive shape, same six-way inversion `Step.from_natRec`,
the same numeral value predicate), so the firing-reduced normal-scrutinee cell SN transfers verbatim — the firing
obligation `succContractumSN` is conditioned on `scrutinee = natSuccCell predecessor`, the recursive call inside the
ι-succ contractum is the `natRec` cell, and scrutinee-congruence is impossible on the normal scrutinee. -/
theorem natRecCellSpine_isStronglyNormalizing_of_normalScrutinee {scope : Nat}
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
              (natRecCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun innerMotive =>
      ∀ {currentZero : RawTerm scope} {currentSucc : RawTerm (scope + 2)},
        IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
        IsStronglyNormalizing (natRecCellSpine innerMotive scrutinee currentZero currentSucc))
    (m := fun currentMotive currentMotiveSuccessors motiveIH => by
      intro currentZero currentSucc currentZeroTerminates currentSuccTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerZero =>
            ∀ {laterSucc : RawTerm (scope + 2)},
              IsStronglyNormalizing laterSucc →
              IsStronglyNormalizing (natRecCellSpine currentMotive scrutinee innerZero laterSucc))
          (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
            intro laterSucc laterSuccTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSucc =>
                  IsStronglyNormalizing
                    (natRecCellSpine currentMotive scrutinee currentInnerZero innerSucc))
                (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
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

/-- **The recursor cell-SN for a NUMERAL scrutinee, modulo the substitution-closure residue — the `natRec` twin.**
The `natRec` analogue of `natElimCellSpine_isStronglyNormalizing_of_natValueScrutinee`: a `natRec` cell whose
scrutinee is a numeral (`IsNatValue`) and whose branches are strongly normalizing is strongly normalizing — GIVEN
`succBranchSubstClosed`.  Same structural numeral induction — a numeral is a normal form, the engine reduces cell SN
to the ι-succ contractum SN, the recursive `natRecCellSpine currentMotive pred …` is SN by the structural inductive
hypothesis (`pred` smaller, the IH universal over branches), and the (generator-agnostic) `succBranchSubstClosed` is
asked to land the substituted contractum.  Carries the SAME HONEST CAVEAT as the `natElim` wrapper:
`succBranchSubstClosed` is UNIVERSALLY FALSE at open scope (`(lam x. x x) (lam x. x x) = Ω` counterexample), so this
RELOCATES rather than eliminates the residue and does NOT close FTGEN-13.1 — the genuine discharge threads Tait
MEMBERSHIP (CR2 + a uniform member-branch closure; the open #1754 work).  The successor witness is identified with
`pred` by `natSuccCell_inj`; the zero case's firing is vacuous (`natZeroCell ≠ natSuccCell _`). -/
theorem natRecCellSpine_isStronglyNormalizing_of_natValueScrutinee {scope : Nat}
    {scrutinee : RawTerm scope}
    (scrutineeIsNatValue : IsNatValue scrutinee)
    (succBranchSubstClosed :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor recursiveResult : RawTerm scope),
        IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
        IsStronglyNormalizing currentSucc → IsNatValue predecessor →
        IsStronglyNormalizing recursiveResult →
        IsStronglyNormalizing
          (RawTerm.subst (RawTermSubst.cons recursiveResult (RawTermSubst.singleton predecessor))
            currentSucc)) :
    ∀ {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)},
      IsStronglyNormalizing motive → IsStronglyNormalizing zeroBranch → IsStronglyNormalizing succBranch →
      IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) := by
  induction scrutineeIsNatValue with
  | zero =>
      intro motive zeroBranch succBranch motiveTerminates zeroBranchTerminates succBranchTerminates
      exact natRecCellSpine_isStronglyNormalizing_of_normalScrutinee
        (isNatValue_impliesStepNormalForm IsNatValue.zero)
        motiveTerminates zeroBranchTerminates succBranchTerminates
        (fun _currentMotive _currentZero _currentSucc _predecessor _ _ _ scrutineeIsSucc =>
          Generator.noConfusion
            (congrArg RawTerm.rootGenerator scrutineeIsSucc :
              Generator.gen_natZero = Generator.gen_natSucc))
  | @succ pred predIsNatValue predIH =>
      intro motive zeroBranch succBranch motiveTerminates zeroBranchTerminates succBranchTerminates
      refine natRecCellSpine_isStronglyNormalizing_of_normalScrutinee
        (isNatValue_impliesStepNormalForm (IsNatValue.succ predIsNatValue))
        motiveTerminates zeroBranchTerminates succBranchTerminates
        (fun currentMotive currentZero currentSucc predecessor currentMotiveSN currentZeroSN
            currentSuccSN scrutineeIsSucc => ?_)
      have predEq : pred = predecessor := natSuccCell_inj scrutineeIsSucc
      subst predEq
      exact succBranchSubstClosed currentMotive currentZero currentSucc pred
        (natRecCellSpine currentMotive pred currentZero currentSucc)
        currentMotiveSN currentZeroSN currentSuccSN predIsNatValue
        (predIH currentMotiveSN currentZeroSN currentSuccSN)

end StepStar
end FX1Poly.Core
