import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Core.ListCanonicalFormsCandidate
import FX1Poly.Typed.HasTypeDescPi

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- listElim cell. -/
def listElimCell {scope : Nat} (scrutinee nilBranch consBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_listElim ()
    (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))

-- Probe 0: ι-rule reduct matches appCell/listElimCell up to defeq.
example {headVal tailVal nilBranch consBranch : RawTerm 0} :
    Step (listElimCell (listConsCell headVal tailVal) nilBranch consBranch)
      (appCell (appCell (appCell consBranch headVal) tailVal)
        (listElimCell tailVal nilBranch consBranch)) :=
  Step.iotaListElimCons

example {nilBranch consBranch : RawTerm 0} :
    Step (listElimCell listNilCell nilBranch consBranch) nilBranch :=
  Step.iotaListElimNil

-- Probe 1: the ABSTRACT recursive computing canonicity, general result predicate.
theorem listElimComputesToValue_probe {isResultValue : RawTerm 0 → Prop}
    {nilBranch consBranch : RawTerm 0}
    (nilBranchValue : isResultValue nilBranch)
    (stepProduces : ∀ (headVal tailVal recResult : RawTerm 0),
        isResultValue recResult →
        ∃ out : RawTerm 0,
          StepStar (appCell (appCell (appCell consBranch headVal) tailVal) recResult) out ∧
          isResultValue out)
    {scrutinee : RawTerm 0} (scrutineeValue : IsListValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (listElimCell scrutinee nilBranch consBranch) out ∧ isResultValue out := by
  induction scrutineeValue with
  | nil => exact ⟨nilBranch, StepStar.single Step.iotaListElimNil, nilBranchValue⟩
  | @cons headVal tailVal _headNormal _tailValue ih =>
      obtain ⟨recResult, recChain, recValue⟩ := ih
      obtain ⟨out, stepChain, outValue⟩ := stepProduces headVal tailVal recResult recValue
      refine ⟨out, ?_, outValue⟩
      have iotaStep :
          StepStar (listElimCell (listConsCell headVal tailVal) nilBranch consBranch)
            (appCell (appCell (appCell consBranch headVal) tailVal)
              (listElimCell tailVal nilBranch consBranch)) :=
        StepStar.single Step.iotaListElimCons
      have congStep :
          StepStar (appCell (appCell (appCell consBranch headVal) tailVal)
              (listElimCell tailVal nilBranch consBranch))
            (appCell (appCell (appCell consBranch headVal) tailVal) recResult) :=
        StepStar.appArgument (appCell (appCell consBranch headVal) tailVal) recChain
      exact StepStar.trans_compose iotaStep (StepStar.trans_compose congStep stepChain)

-- Probe 2: the length step `λ_. λ_. λr. natSucc r` produces `natSucc rec` (3 β-steps).
def lengthNatStep : RawTerm 0 :=
  lamCell (lamCell (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 3)))))

example (headVal tailVal recResult : RawTerm 0) :
    StepStar (appCell (appCell (appCell lengthNatStep headVal) tailVal) recResult)
      (natSuccCell recResult) := by
  have beta1 : Step (appCell lengthNatStep headVal)
      (lamCell (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 2))))) := Step.beta
  have beta2 : Step (appCell (lamCell (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 2))))) tailVal)
      (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) := Step.beta
  have beta3 : Step (appCell (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) recResult)
      (natSuccCell recResult) := Step.beta
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.appFunction (StepStar.single beta1)))
    (StepStar.trans_compose
      (StepStar.appFunction (StepStar.single beta2))
      (StepStar.single beta3))

-- Probe 3: list length computing canonicity via the abstract theorem.
example {scrutinee : RawTerm 0} (scrutineeValue : IsListValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (listElimCell scrutinee natZeroCell lengthNatStep) out ∧ IsNatNumeral out :=
  listElimComputesToValue_probe (isResultValue := IsNatNumeral)
    (nilBranch := natZeroCell) (consBranch := lengthNatStep)
    IsNatNumeral.zero
    (fun headVal tailVal recResult recNumeral =>
      ⟨natSuccCell recResult, by
        have beta1 : Step (appCell lengthNatStep headVal)
            (lamCell (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 2))))) := Step.beta
        have beta2 : Step (appCell (lamCell (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 2))))) tailVal)
            (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) := Step.beta
        have beta3 : Step (appCell (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) recResult)
            (natSuccCell recResult) := Step.beta
        exact StepStar.trans_compose
          (StepStar.appFunction (StepStar.appFunction (StepStar.single beta1)))
          (StepStar.trans_compose
            (StepStar.appFunction (StepStar.single beta2))
            (StepStar.single beta3)),
        IsNatNumeral.succ recNumeral⟩)
    scrutineeValue

end FX1Poly.Typed

#print axioms FX1Poly.Typed.listElimComputesToValue_probe
