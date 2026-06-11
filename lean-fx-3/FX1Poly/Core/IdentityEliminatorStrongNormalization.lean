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
reducibility.

## Proof shape

A triple nested accessibility induction on `(motive, witness, baseCase)` — the Phase-Z spine carries the
motive (under two binders) first, the witness (the active child whose `refl` form fires the ι-rule
`idJ motive base (refl x) ↝ base`), and the base (passive child) last.  At the innermost point the
`Step.from_idJ` (resp. `from_idStrictRec`) inversion splits four ways: the ι-fire lands on the current base
(SN by its own accessibility), motive-congruence recurses on the outer (motive) induction hypothesis,
base-congruence on the inner (base) induction hypothesis, and witness-congruence on the middle (witness)
induction hypothesis.  The motive and base need not be normal: their congruence reducts are discharged by the
motive / base inductions.

## Zero-axiom verification

`Acc.ndrec` (three nested), `Step.from_idJ` / `Step.from_idStrictRec` (cased Step ctors, no propext),
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
    {scope : Nat} {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (motiveTerminates : IsStronglyNormalizing motive)
    (baseCaseTerminates : IsStronglyNormalizing baseCase)
    (witnessTerminates : IsStronglyNormalizing witness) :
    IsStronglyNormalizing
      (.mkGen .gen_idJ ()
        (.childCons motive
          (.childCons baseCase (.childCons witness .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentMotive =>
      ∀ {currentWitness currentBase : RawTerm scope},
        IsStronglyNormalizing currentWitness → IsStronglyNormalizing currentBase →
          IsStronglyNormalizing
            (.mkGen .gen_idJ ()
              (.childCons currentMotive
                (.childCons currentBase (.childCons currentWitness .childNil)))))
    (m := fun currentMotive currentMotiveSuccessors motiveIH => by
      intro currentWitness currentBase currentWitnessTerminates currentBaseTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerWitness =>
            ∀ {innerBase : RawTerm scope},
              IsStronglyNormalizing innerBase →
                IsStronglyNormalizing
                  (.mkGen .gen_idJ ()
                    (.childCons currentMotive
                      (.childCons innerBase (.childCons innerWitness .childNil)))))
          (m := fun currentInnerWitness currentInnerWitnessSuccessors witnessIH => by
            intro innerBase innerBaseTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerBase' =>
                  IsStronglyNormalizing
                    (.mkGen .gen_idJ ()
                      (.childCons currentMotive
                        (.childCons innerBase' (.childCons currentInnerWitness .childNil)))))
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
                      | inl motiveCongruence =>
                          obtain ⟨motiveAfter, targetEq, motiveStep⟩ := motiveCongruence
                          rw [targetEq]
                          exact motiveIH motiveAfter motiveStep
                            (Acc.intro currentInnerWitness currentInnerWitnessSuccessors)
                            (Acc.intro currentInnerBase currentInnerBaseSuccessors)
                      | inr restAfterMotive =>
                          cases restAfterMotive with
                          | inl baseCongruence =>
                              obtain ⟨baseAfter, targetEq, baseStep⟩ := baseCongruence
                              rw [targetEq]
                              exact baseIH baseAfter baseStep
                          | inr witnessCongruence =>
                              obtain ⟨witnessAfter, targetEq, witnessStep⟩ := witnessCongruence
                              rw [targetEq]
                              exact witnessIH witnessAfter witnessStep
                                (Acc.intro currentInnerBase currentInnerBaseSuccessors))
                innerBaseTerminates)
          currentWitnessTerminates currentBaseTerminates))
    motiveTerminates)
    witnessTerminates baseCaseTerminates

/-- **`idStrictRec` is strongly normalizing when its base case and witness are.**  Identical to
`idJ_isStronglyNormalizing_of_strongly_normalizing_base`: the strict identity eliminator has the same
`(base, witness)` child spine and the same single ι-rule (`idStrictRec … (refl w) ↝ base`), inverted by
`Step.from_idStrictRec`. -/
theorem idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base
    {scope : Nat} {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (motiveTerminates : IsStronglyNormalizing motive)
    (baseCaseTerminates : IsStronglyNormalizing baseCase)
    (witnessTerminates : IsStronglyNormalizing witness) :
    IsStronglyNormalizing
      (.mkGen .gen_idStrictRec ()
        (.childCons motive
          (.childCons baseCase (.childCons witness .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentMotive =>
      ∀ {currentWitness currentBase : RawTerm scope},
        IsStronglyNormalizing currentWitness → IsStronglyNormalizing currentBase →
          IsStronglyNormalizing
            (.mkGen .gen_idStrictRec ()
              (.childCons currentMotive
                (.childCons currentBase (.childCons currentWitness .childNil)))))
    (m := fun currentMotive currentMotiveSuccessors motiveIH => by
      intro currentWitness currentBase currentWitnessTerminates currentBaseTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerWitness =>
            ∀ {innerBase : RawTerm scope},
              IsStronglyNormalizing innerBase →
                IsStronglyNormalizing
                  (.mkGen .gen_idStrictRec ()
                    (.childCons currentMotive
                      (.childCons innerBase (.childCons innerWitness .childNil)))))
          (m := fun currentInnerWitness currentInnerWitnessSuccessors witnessIH => by
            intro innerBase innerBaseTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerBase' =>
                  IsStronglyNormalizing
                    (.mkGen .gen_idStrictRec ()
                      (.childCons currentMotive
                        (.childCons innerBase' (.childCons currentInnerWitness .childNil)))))
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
                      | inl motiveCongruence =>
                          obtain ⟨motiveAfter, targetEq, motiveStep⟩ := motiveCongruence
                          rw [targetEq]
                          exact motiveIH motiveAfter motiveStep
                            (Acc.intro currentInnerWitness currentInnerWitnessSuccessors)
                            (Acc.intro currentInnerBase currentInnerBaseSuccessors)
                      | inr restAfterMotive =>
                          cases restAfterMotive with
                          | inl baseCongruence =>
                              obtain ⟨baseAfter, targetEq, baseStep⟩ := baseCongruence
                              rw [targetEq]
                              exact baseIH baseAfter baseStep
                          | inr witnessCongruence =>
                              obtain ⟨witnessAfter, targetEq, witnessStep⟩ := witnessCongruence
                              rw [targetEq]
                              exact witnessIH witnessAfter witnessStep
                                (Acc.intro currentInnerBase currentInnerBaseSuccessors))
                innerBaseTerminates)
          currentWitnessTerminates currentBaseTerminates))
    motiveTerminates)
    witnessTerminates baseCaseTerminates

end StepStar
end FX1Poly.Core
