import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Core.OptionCanonicalFormsCandidate
import FX1Poly.Core.EitherCanonicalFormsCandidate
import FX1Poly.Typed.HasTypeDescPi

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

def optionMatchCell {scope : Nat} (scrutinee noneBranch someBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_optionMatch ()
    (.childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil)))

def eitherMatchCell {scope : Nat} (scrutinee leftBranch rightBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherMatch ()
    (.childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)))

-- Probe 0: ι reduct shapes.
example {payload n s : RawTerm 0} :
    Step (optionMatchCell (optionSomeCell payload) n s) (appCell s payload) :=
  Step.iotaOptionMatchSome
example {n s : RawTerm 0} : Step (optionMatchCell optionNoneCell n s) n :=
  Step.iotaOptionMatchNone

-- Probe 1: abstract optionMatch computing canonicity (non-recursive, function-branch).
theorem optionMatchComputesToValue_probe {isResultValue : RawTerm 0 → Prop}
    {noneBranch someBranch : RawTerm 0}
    (noneBranchValue : isResultValue noneBranch)
    (stepProduces : ∀ payload : RawTerm 0, RawTerm.isStepNormalForm payload →
        ∃ out : RawTerm 0, StepStar (appCell someBranch payload) out ∧ isResultValue out)
    {scrutinee : RawTerm 0} (scrutineeValue : isOptionValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell scrutinee noneBranch someBranch) out ∧ isResultValue out := by
  rcases scrutineeValue with noneEq | ⟨payload, someEq, payloadNormal⟩
  · subst noneEq
    exact ⟨noneBranch, StepStar.single Step.iotaOptionMatchNone, noneBranchValue⟩
  · subst someEq
    obtain ⟨out, appChain, outValue⟩ := stepProduces payload payloadNormal
    exact ⟨out, StepStar.trans_compose (StepStar.single Step.iotaOptionMatchSome) appChain, outValue⟩

-- Probe 2: abstract eitherMatch computing canonicity.
theorem eitherMatchComputesToValue_probe {isResultValue : RawTerm 0 → Prop}
    {leftBranch rightBranch : RawTerm 0}
    (leftProduces : ∀ payload : RawTerm 0, RawTerm.isStepNormalForm payload →
        ∃ out : RawTerm 0, StepStar (appCell leftBranch payload) out ∧ isResultValue out)
    (rightProduces : ∀ payload : RawTerm 0, RawTerm.isStepNormalForm payload →
        ∃ out : RawTerm 0, StepStar (appCell rightBranch payload) out ∧ isResultValue out)
    {scrutinee : RawTerm 0} (scrutineeValue : isEitherValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (eitherMatchCell scrutinee leftBranch rightBranch) out ∧ isResultValue out := by
  rcases scrutineeValue with ⟨payload, inlEq, payloadNormal⟩ | ⟨payload, inrEq, payloadNormal⟩
  · subst inlEq
    obtain ⟨out, appChain, outValue⟩ := leftProduces payload payloadNormal
    exact ⟨out, StepStar.trans_compose (StepStar.single Step.iotaEitherMatchInl) appChain, outValue⟩
  · subst inrEq
    obtain ⟨out, appChain, outValue⟩ := rightProduces payload payloadNormal
    exact ⟨out, StepStar.trans_compose (StepStar.single Step.iotaEitherMatchInr) appChain, outValue⟩

-- Probe 3: constant fold — λ_. natZero, isResultValue := IsNatNumeral.
example {scrutinee : RawTerm 0} (scrutineeValue : isOptionValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell scrutinee natZeroCell (lamCell (natZeroCell : RawTerm 1))) out ∧
      IsNatNumeral out :=
  optionMatchComputesToValue_probe (isResultValue := IsNatNumeral)
    IsNatNumeral.zero
    (fun payload _ => ⟨natZeroCell, StepStar.single Step.beta, IsNatNumeral.zero⟩)
    scrutineeValue

-- Probe 4: identity fold — λx. x, USES the payload (isResultValue := isStepNormalForm).
example {scrutinee : RawTerm 0} (scrutineeValue : isOptionValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell scrutinee boolTrueCell (lamCell (variableCell (⟨0, by decide⟩ : Fin 1)))) out ∧
      RawTerm.isStepNormalForm out :=
  optionMatchComputesToValue_probe (isResultValue := RawTerm.isStepNormalForm)
    (by decide)
    (fun payload payloadNormal => ⟨payload, StepStar.single Step.beta, payloadNormal⟩)
    scrutineeValue

end FX1Poly.Typed

#print axioms FX1Poly.Typed.optionMatchComputesToValue_probe
#print axioms FX1Poly.Typed.eitherMatchComputesToValue_probe
