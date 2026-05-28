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

end StepStar
end LeanFX2.Foundation.PolyCell.Core
