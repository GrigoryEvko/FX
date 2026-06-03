import FX1Poly.Core.StrongNormalizationIotaRedexes

/-! # Foundation/PolyCell/Core/IdentityEliminatorStrongNormalization
    — `idJ` / `idStrictRec` are SN when base AND witness are SN (the base×witness two-dimensional induction)

`StrongNormalizationIotaRedexes.lean` proves the identity eliminators SN when the BASE is NORMAL and the
witness is SN, and its own docstring flags the strengthening: *"The strictly-more-general 'base merely SN'
form would need a nested two-dimensional accessibility induction over base × witness."*  This file supplies
exactly that — the SN-base strengthening, the identity-eliminator analogue of
`boolElim_isStronglyNormalizing_of_strongly_normalizing_branches` (`BoolElimStrongNormalization.lean`).

As in the `boolElim` case, the strengthening matters for **eliminator reducibility**: in the Tait argument
the base case is a MEMBER of the motive's reducibility candidate, hence strongly normalizing but not
necessarily normal.  These lemmas are the iota-head-expansion SN foundation for `idJ` / `idStrictRec`
reducibility (toward SN-068 / SN-069).

## Proof shape

A double nested accessibility induction on `(witness, baseCase)` — the witness is the active child (its `refl`
form fires the ι-rule `idJ base (refl x) ↝ base`), the base the passive child.  At the innermost point the
`Step.from_idJ` (resp. `from_idStrictRec`) inversion splits three ways: the ι-fire lands on the current base
(SN by its own accessibility), base-congruence recurses on the inner (base) induction hypothesis, and
witness-congruence on the outer (witness) induction hypothesis.  The base is no longer required normal because
its congruence reduct is now discharged by the base induction rather than refuted.

## Zero-axiom verification

`Acc.ndrec` (two nested), `Step.from_idJ` / `Step.from_idStrictRec` (cased Step ctors, no propext),
`Acc.intro`, and `rw` on the target equalities.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- **`idJ` is strongly normalizing when its base case and witness are.**  The SN-base strengthening of
`idJ_isStronglyNormalizing_of_normal_base`, by the base×witness two-dimensional accessibility induction (the
ι-fire lands on the current base, SN by its own accessibility; base/witness congruences recurse on the
inner/outer induction hypothesis). -/
theorem idJ_isStronglyNormalizing_of_strongly_normalizing_base
    {scope : Nat} {baseCase witness : RawTerm scope}
    (baseCaseTerminates : IsStronglyNormalizing baseCase)
    (witnessTerminates : IsStronglyNormalizing witness) :
    IsStronglyNormalizing
      (.mkGen .gen_idJ ()
        (.childCons baseCase (.childCons witness .childNil)) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentWitness =>
      ∀ {currentBase : RawTerm scope},
        IsStronglyNormalizing currentBase →
          IsStronglyNormalizing
            (.mkGen .gen_idJ ()
              (.childCons currentBase (.childCons currentWitness .childNil))))
    (m := fun currentWitness _currentWitnessSuccessors witnessIH => by
      intro currentBase currentBaseTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerBase =>
            IsStronglyNormalizing
              (.mkGen .gen_idJ ()
                (.childCons innerBase (.childCons currentWitness .childNil))))
          (m := fun currentInnerBase currentInnerBaseSuccessors baseIH => by
            apply Acc.intro
            intro targetTerm idJStep
            cases Step.from_idJ idJStep with
            | inl iotaReflBase =>
                obtain ⟨_rawWitness, _witnessIsRefl, targetIsBase⟩ := iotaReflBase
                rw [targetIsBase]
                exact Acc.intro currentInnerBase currentInnerBaseSuccessors
            | inr congruenceBranch =>
                cases congruenceBranch with
                | inl baseCongruence =>
                    obtain ⟨baseAfter, targetEq, baseStep⟩ := baseCongruence
                    rw [targetEq]
                    exact baseIH baseAfter baseStep
                | inr witnessCongruence =>
                    obtain ⟨witnessAfter, targetEq, witnessStep⟩ := witnessCongruence
                    rw [targetEq]
                    exact witnessIH witnessAfter witnessStep
                      (Acc.intro currentInnerBase currentInnerBaseSuccessors))
          currentBaseTerminates)
    witnessTerminates)
    baseCaseTerminates

/-- **`idStrictRec` is strongly normalizing when its base case and witness are.**  Identical to
`idJ_isStronglyNormalizing_of_strongly_normalizing_base`: the strict identity eliminator has the same
`(base, witness)` child spine and the same single ι-rule (`idStrictRec … (refl w) ↝ base`), inverted by
`Step.from_idStrictRec`. -/
theorem idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base
    {scope : Nat} {baseCase witness : RawTerm scope}
    (baseCaseTerminates : IsStronglyNormalizing baseCase)
    (witnessTerminates : IsStronglyNormalizing witness) :
    IsStronglyNormalizing
      (.mkGen .gen_idStrictRec ()
        (.childCons baseCase (.childCons witness .childNil)) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentWitness =>
      ∀ {currentBase : RawTerm scope},
        IsStronglyNormalizing currentBase →
          IsStronglyNormalizing
            (.mkGen .gen_idStrictRec ()
              (.childCons currentBase (.childCons currentWitness .childNil))))
    (m := fun currentWitness _currentWitnessSuccessors witnessIH => by
      intro currentBase currentBaseTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerBase =>
            IsStronglyNormalizing
              (.mkGen .gen_idStrictRec ()
                (.childCons innerBase (.childCons currentWitness .childNil))))
          (m := fun currentInnerBase currentInnerBaseSuccessors baseIH => by
            apply Acc.intro
            intro targetTerm idStrictRecStep
            cases Step.from_idStrictRec idStrictRecStep with
            | inl iotaReflBase =>
                obtain ⟨_rawWitness, _witnessIsRefl, targetIsBase⟩ := iotaReflBase
                rw [targetIsBase]
                exact Acc.intro currentInnerBase currentInnerBaseSuccessors
            | inr congruenceBranch =>
                cases congruenceBranch with
                | inl baseCongruence =>
                    obtain ⟨baseAfter, targetEq, baseStep⟩ := baseCongruence
                    rw [targetEq]
                    exact baseIH baseAfter baseStep
                | inr witnessCongruence =>
                    obtain ⟨witnessAfter, targetEq, witnessStep⟩ := witnessCongruence
                    rw [targetEq]
                    exact witnessIH witnessAfter witnessStep
                      (Acc.intro currentInnerBase currentInnerBaseSuccessors))
          currentBaseTerminates)
    witnessTerminates)
    baseCaseTerminates

end StepStar
end FX1Poly.Core
