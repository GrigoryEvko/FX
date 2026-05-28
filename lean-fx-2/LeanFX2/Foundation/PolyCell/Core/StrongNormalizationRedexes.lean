import LeanFX2.Foundation.PolyCell.Core.StrongNormalizationConstructors

/-! # Foundation/PolyCell/Core/StrongNormalizationRedexes
    - first SN closure proofs for root-reducing redexes

The leaf and constructor files cover normal leaves plus congruence-only
wrappers.  This file starts the next layer: terms that can reduce at the root.
Each theorem must account for both the root reduct and congruence steps inside
the redex's children.

This is still not global SN, not a reducibility predicate, and not the
fundamental theorem.  It is a small audited bridge from congruence-only
accessibility into iota/root-reduction accessibility.
-/

namespace LeanFX2.Foundation.PolyCell.Core
namespace StepStar

/-- First projection of an explicitly-normalizing pair is strongly normalizing.

The root iota reduct is the first component.  Congruence steps inside the pair
are handled by nested accessibility induction on the two components. -/
theorem fstPair_isStronglyNormalizing_of_components {scope : Nat}
    {first second : RawTerm scope}
    (firstTerminates : IsStronglyNormalizing first)
    (secondTerminates : IsStronglyNormalizing second) :
    IsStronglyNormalizing
      (.mkGen .gen_fst ()
        (.childCons
          (.mkGen .gen_pair ()
            (.childCons first (.childCons second .childNil)))
          .childNil) : RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentFirst =>
      ∀ {currentSecond : RawTerm scope},
        IsStronglyNormalizing currentSecond →
          IsStronglyNormalizing
            (.mkGen .gen_fst ()
              (.childCons
                (.mkGen .gen_pair ()
                  (.childCons currentFirst
                    (.childCons currentSecond .childNil)))
                .childNil) : RawTerm scope))
    (m := fun currentFirst currentFirstSuccessors firstChildIH => by
      intro currentSecond currentSecondTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerSecond =>
            IsStronglyNormalizing
              (.mkGen .gen_fst ()
                (.childCons
                  (.mkGen .gen_pair ()
                    (.childCons currentFirst
                      (.childCons innerSecond .childNil)))
                  .childNil) : RawTerm scope))
          (m := fun currentSecond currentSecondSuccessors secondChildIH =>
            Acc.intro
              (.mkGen .gen_fst ()
                (.childCons
                  (.mkGen .gen_pair ()
                    (.childCons currentFirst
                      (.childCons currentSecond .childNil)))
                  .childNil) : RawTerm scope)
              (fun targetTerm parentStep => by
                cases Step.from_fst parentStep with
                | inl iotaBranch =>
                    obtain ⟨firstValue, secondValue, pairEq, targetEq⟩ :=
                      iotaBranch
                    cases pairEq
                    rw [targetEq]
                    exact Acc.intro currentFirst currentFirstSuccessors
                | inr congBranch =>
                    obtain ⟨argAfter, targetEq, pairStep⟩ := congBranch
                    cases Step.from_pair pairStep with
                    | inl firstBranch =>
                        obtain ⟨firstAfter, pairEq, firstStep⟩ := firstBranch
                        rw [targetEq, pairEq]
                        exact firstChildIH firstAfter firstStep
                          (Acc.intro currentSecond currentSecondSuccessors)
                    | inr secondBranch =>
                        obtain ⟨secondAfter, pairEq, secondStep⟩ :=
                          secondBranch
                        rw [targetEq, pairEq]
                        exact secondChildIH secondAfter secondStep))
          currentSecondTerminates)
    firstTerminates)
    secondTerminates

/-- Second projection of an explicitly-normalizing pair is strongly
normalizing.  Symmetric to `fstPair_isStronglyNormalizing_of_components`, with
the root iota reduct selecting the second component. -/
theorem sndPair_isStronglyNormalizing_of_components {scope : Nat}
    {first second : RawTerm scope}
    (firstTerminates : IsStronglyNormalizing first)
    (secondTerminates : IsStronglyNormalizing second) :
    IsStronglyNormalizing
      (.mkGen .gen_snd ()
        (.childCons
          (.mkGen .gen_pair ()
            (.childCons first (.childCons second .childNil)))
          .childNil) : RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentFirst =>
      ∀ {currentSecond : RawTerm scope},
        IsStronglyNormalizing currentSecond →
          IsStronglyNormalizing
            (.mkGen .gen_snd ()
              (.childCons
                (.mkGen .gen_pair ()
                  (.childCons currentFirst
                    (.childCons currentSecond .childNil)))
                .childNil) : RawTerm scope))
    (m := fun currentFirst currentFirstSuccessors firstChildIH => by
      intro currentSecond currentSecondTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerSecond =>
            IsStronglyNormalizing
              (.mkGen .gen_snd ()
                (.childCons
                  (.mkGen .gen_pair ()
                    (.childCons currentFirst
                      (.childCons innerSecond .childNil)))
                  .childNil) : RawTerm scope))
          (m := fun currentSecond currentSecondSuccessors secondChildIH =>
            Acc.intro
              (.mkGen .gen_snd ()
                (.childCons
                  (.mkGen .gen_pair ()
                    (.childCons currentFirst
                      (.childCons currentSecond .childNil)))
                  .childNil) : RawTerm scope)
              (fun targetTerm parentStep => by
                cases Step.from_snd parentStep with
                | inl iotaBranch =>
                    obtain ⟨firstValue, secondValue, pairEq, targetEq⟩ :=
                      iotaBranch
                    cases pairEq
                    rw [targetEq]
                    exact Acc.intro currentSecond currentSecondSuccessors
                | inr congBranch =>
                    obtain ⟨argAfter, targetEq, pairStep⟩ := congBranch
                    cases Step.from_pair pairStep with
                    | inl firstBranch =>
                        obtain ⟨firstAfter, pairEq, firstStep⟩ := firstBranch
                        rw [targetEq, pairEq]
                        exact firstChildIH firstAfter firstStep
                          (Acc.intro currentSecond currentSecondSuccessors)
                    | inr secondBranch =>
                        obtain ⟨secondAfter, pairEq, secondStep⟩ :=
                          secondBranch
                        rw [targetEq, pairEq]
                        exact secondChildIH secondAfter secondStep))
          currentSecondTerminates)
    firstTerminates)
    secondTerminates

/-- Boolean elimination on the literal `true` is strongly normalizing when both
branches are strongly normalizing.

The root iota reduct is the then-branch.  Congruence at the scrutinee is
impossible because `boolTrue` is a normal leaf; congruence in either branch is
handled by nested accessibility induction on the branches. -/
theorem boolElimTrue_isStronglyNormalizing_of_branches {scope : Nat}
    {thenBranch elseBranch : RawTerm scope}
    (thenTerminates : IsStronglyNormalizing thenBranch)
    (elseTerminates : IsStronglyNormalizing elseBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_boolElim ()
        (.childCons
          (.mkGen .gen_boolTrue () .childNil)
          (.childCons thenBranch (.childCons elseBranch .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentThen =>
      ∀ {currentElse : RawTerm scope},
        IsStronglyNormalizing currentElse →
          IsStronglyNormalizing
            (.mkGen .gen_boolElim ()
              (.childCons
                (.mkGen .gen_boolTrue () .childNil)
                (.childCons currentThen
                  (.childCons currentElse .childNil))) : RawTerm scope))
    (m := fun currentThen currentThenSuccessors thenBranchIH => by
      intro currentElse currentElseTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerElse =>
            IsStronglyNormalizing
              (.mkGen .gen_boolElim ()
                (.childCons
                  (.mkGen .gen_boolTrue () .childNil)
                  (.childCons currentThen
                    (.childCons innerElse .childNil))) : RawTerm scope))
          (m := fun currentElse currentElseSuccessors elseBranchIH =>
            Acc.intro
              (.mkGen .gen_boolElim ()
                (.childCons
                  (.mkGen .gen_boolTrue () .childNil)
                  (.childCons currentThen
                    (.childCons currentElse .childNil))) : RawTerm scope)
              (fun targetTerm parentStep => by
                cases Step.from_boolElim parentStep with
                | inl trueBranch =>
                    obtain ⟨_, targetEq⟩ := trueBranch
                    rw [targetEq]
                    exact Acc.intro currentThen currentThenSuccessors
                | inr restAfterTrue =>
                    cases restAfterTrue with
                    | inl falseBranch =>
                        obtain ⟨scrutineeEq, _⟩ := falseBranch
                        cases scrutineeEq
                    | inr restAfterFalse =>
                        cases restAfterFalse with
                        | inl scrutineeBranch =>
                            obtain ⟨_, _, scrutineeStep⟩ := scrutineeBranch
                            exact False.elim (noStep_boolTrue scrutineeStep)
                        | inr restAfterScrutinee =>
                            cases restAfterScrutinee with
                            | inl thenBranchStep =>
                                obtain ⟨thenAfter, targetEq, thenStep⟩ :=
                                  thenBranchStep
                                rw [targetEq]
                                exact thenBranchIH thenAfter thenStep
                                  (Acc.intro currentElse currentElseSuccessors)
                            | inr elseBranchStep =>
                                obtain ⟨elseAfter, targetEq, elseStep⟩ :=
                                  elseBranchStep
                                rw [targetEq]
                                exact elseBranchIH elseAfter elseStep))
          currentElseTerminates)
    thenTerminates)
    elseTerminates

/-- Boolean elimination on the literal `false` is strongly normalizing when
both branches are strongly normalizing.  Symmetric to the `true` case, with the
root iota reduct selecting the else-branch. -/
theorem boolElimFalse_isStronglyNormalizing_of_branches {scope : Nat}
    {thenBranch elseBranch : RawTerm scope}
    (thenTerminates : IsStronglyNormalizing thenBranch)
    (elseTerminates : IsStronglyNormalizing elseBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_boolElim ()
        (.childCons
          (.mkGen .gen_boolFalse () .childNil)
          (.childCons thenBranch (.childCons elseBranch .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentThen =>
      ∀ {currentElse : RawTerm scope},
        IsStronglyNormalizing currentElse →
          IsStronglyNormalizing
            (.mkGen .gen_boolElim ()
              (.childCons
                (.mkGen .gen_boolFalse () .childNil)
                (.childCons currentThen
                  (.childCons currentElse .childNil))) : RawTerm scope))
    (m := fun currentThen currentThenSuccessors thenBranchIH => by
      intro currentElse currentElseTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerElse =>
            IsStronglyNormalizing
              (.mkGen .gen_boolElim ()
                (.childCons
                  (.mkGen .gen_boolFalse () .childNil)
                  (.childCons currentThen
                    (.childCons innerElse .childNil))) : RawTerm scope))
          (m := fun currentElse currentElseSuccessors elseBranchIH =>
            Acc.intro
              (.mkGen .gen_boolElim ()
                (.childCons
                  (.mkGen .gen_boolFalse () .childNil)
                  (.childCons currentThen
                    (.childCons currentElse .childNil))) : RawTerm scope)
              (fun targetTerm parentStep => by
                cases Step.from_boolElim parentStep with
                | inl trueBranch =>
                    obtain ⟨scrutineeEq, _⟩ := trueBranch
                    cases scrutineeEq
                | inr restAfterTrue =>
                    cases restAfterTrue with
                    | inl falseBranch =>
                        obtain ⟨_, targetEq⟩ := falseBranch
                        rw [targetEq]
                        exact Acc.intro currentElse currentElseSuccessors
                    | inr restAfterFalse =>
                        cases restAfterFalse with
                        | inl scrutineeBranch =>
                            obtain ⟨_, _, scrutineeStep⟩ := scrutineeBranch
                            exact False.elim (noStep_boolFalse scrutineeStep)
                        | inr restAfterScrutinee =>
                            cases restAfterScrutinee with
                            | inl thenBranchStep =>
                                obtain ⟨thenAfter, targetEq, thenStep⟩ :=
                                  thenBranchStep
                                rw [targetEq]
                                exact thenBranchIH thenAfter thenStep
                                  (Acc.intro currentElse currentElseSuccessors)
                            | inr elseBranchStep =>
                                obtain ⟨elseAfter, targetEq, elseStep⟩ :=
                                  elseBranchStep
                                rw [targetEq]
                                exact elseBranchIH elseAfter elseStep))
          currentElseTerminates)
    thenTerminates)
    elseTerminates

/-- Identity elimination on a reflexivity witness is strongly normalizing when
the base case and raw witness are strongly normalizing.

The root iota reduct is the base case.  Congruence in the base case is handled
directly, while congruence in the reflexivity witness is inverted through
`Step.from_refl` before reusing the witness accessibility induction. -/
theorem idJRefl_isStronglyNormalizing_of_base_witness {scope : Nat}
    {baseCase rawWitness : RawTerm scope}
    (baseTerminates : IsStronglyNormalizing baseCase)
    (witnessTerminates : IsStronglyNormalizing rawWitness) :
    IsStronglyNormalizing
      (.mkGen .gen_idJ ()
        (.childCons baseCase
          (.childCons
            (.mkGen .gen_refl () (.childCons rawWitness .childNil))
            .childNil)) : RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentBase =>
      ∀ {currentWitness : RawTerm scope},
        IsStronglyNormalizing currentWitness →
          IsStronglyNormalizing
            (.mkGen .gen_idJ ()
              (.childCons currentBase
                (.childCons
                  (.mkGen .gen_refl ()
                    (.childCons currentWitness .childNil))
                  .childNil)) : RawTerm scope))
    (m := fun currentBase currentBaseSuccessors baseCaseIH => by
      intro currentWitness currentWitnessTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerWitness =>
            IsStronglyNormalizing
              (.mkGen .gen_idJ ()
                (.childCons currentBase
                  (.childCons
                    (.mkGen .gen_refl ()
                      (.childCons innerWitness .childNil))
                    .childNil)) : RawTerm scope))
          (m := fun currentWitness currentWitnessSuccessors witnessIH =>
            Acc.intro
              (.mkGen .gen_idJ ()
                (.childCons currentBase
                  (.childCons
                    (.mkGen .gen_refl ()
                      (.childCons currentWitness .childNil))
                    .childNil)) : RawTerm scope)
              (fun targetTerm parentStep => by
                cases Step.from_idJ parentStep with
                | inl iotaBranch =>
                    obtain ⟨iotaWitness, witnessEq, targetEq⟩ := iotaBranch
                    cases witnessEq
                    rw [targetEq]
                    exact Acc.intro currentBase currentBaseSuccessors
                | inr restAfterIota =>
                    cases restAfterIota with
                    | inl baseBranch =>
                        obtain ⟨baseAfter, targetEq, baseStep⟩ := baseBranch
                        rw [targetEq]
                        exact baseCaseIH baseAfter baseStep
                          (Acc.intro currentWitness currentWitnessSuccessors)
                    | inr witnessBranch =>
                        obtain ⟨witnessAfter, targetEq, witnessStep⟩ :=
                          witnessBranch
                        obtain
                          ⟨rawWitnessAfter, witnessAfterEq,
                            rawWitnessStep⟩ := Step.from_refl witnessStep
                        rw [targetEq, witnessAfterEq]
                        exact witnessIH rawWitnessAfter rawWitnessStep))
          currentWitnessTerminates)
    baseTerminates)
    witnessTerminates

/-- Strict identity recursion on a reflexivity witness is strongly normalizing
when the base case and raw witness are strongly normalizing.

This is the strict-recursion sibling of
`idJRefl_isStronglyNormalizing_of_base_witness`; the substrate reduction shape
is identical, but the outer generator is `gen_idStrictRec`. -/
theorem idStrictRecRefl_isStronglyNormalizing_of_base_witness {scope : Nat}
    {baseCase rawWitness : RawTerm scope}
    (baseTerminates : IsStronglyNormalizing baseCase)
    (witnessTerminates : IsStronglyNormalizing rawWitness) :
    IsStronglyNormalizing
      (.mkGen .gen_idStrictRec ()
        (.childCons baseCase
          (.childCons
            (.mkGen .gen_refl () (.childCons rawWitness .childNil))
            .childNil)) : RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentBase =>
      ∀ {currentWitness : RawTerm scope},
        IsStronglyNormalizing currentWitness →
          IsStronglyNormalizing
            (.mkGen .gen_idStrictRec ()
              (.childCons currentBase
                (.childCons
                  (.mkGen .gen_refl ()
                    (.childCons currentWitness .childNil))
                  .childNil)) : RawTerm scope))
    (m := fun currentBase currentBaseSuccessors baseCaseIH => by
      intro currentWitness currentWitnessTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerWitness =>
            IsStronglyNormalizing
              (.mkGen .gen_idStrictRec ()
                (.childCons currentBase
                  (.childCons
                    (.mkGen .gen_refl ()
                      (.childCons innerWitness .childNil))
                    .childNil)) : RawTerm scope))
          (m := fun currentWitness currentWitnessSuccessors witnessIH =>
            Acc.intro
              (.mkGen .gen_idStrictRec ()
                (.childCons currentBase
                  (.childCons
                    (.mkGen .gen_refl ()
                      (.childCons currentWitness .childNil))
                    .childNil)) : RawTerm scope)
              (fun targetTerm parentStep => by
                cases Step.from_idStrictRec parentStep with
                | inl iotaBranch =>
                    obtain ⟨iotaWitness, witnessEq, targetEq⟩ := iotaBranch
                    cases witnessEq
                    rw [targetEq]
                    exact Acc.intro currentBase currentBaseSuccessors
                | inr restAfterIota =>
                    cases restAfterIota with
                    | inl baseBranch =>
                        obtain ⟨baseAfter, targetEq, baseStep⟩ := baseBranch
                        rw [targetEq]
                        exact baseCaseIH baseAfter baseStep
                          (Acc.intro currentWitness currentWitnessSuccessors)
                    | inr witnessBranch =>
                        obtain ⟨witnessAfter, targetEq, witnessStep⟩ :=
                          witnessBranch
                        obtain
                          ⟨rawWitnessAfter, witnessAfterEq,
                            rawWitnessStep⟩ := Step.from_refl witnessStep
                        rw [targetEq, witnessAfterEq]
                        exact witnessIH rawWitnessAfter rawWitnessStep))
          currentWitnessTerminates)
    baseTerminates)
    witnessTerminates

end StepStar
end LeanFX2.Foundation.PolyCell.Core
