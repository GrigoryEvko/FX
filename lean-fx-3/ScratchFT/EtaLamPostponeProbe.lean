import FX1Poly.Core.StrongNormalizationUnion
import FX1Poly.Core.StepEta
import FX1Poly.Core.StepSubst

/-! Probe (NEVER committed): OSN-B3 — etaLam η-postponement over β.
    Given `etaLam : Step.eta (etaLamSource f) f` then a β/ι-step `f → c`, reorder to a single β/ι-step
    `etaLamSource f → etaLamSource c` (congruence lift through lam ∘ app ∘ weaken) followed by one
    etaLam η-step `etaLamSource c →η c` (the βη*-tail).  This is the etaLam case of
    QuasiCommutesRightOverLeft Step Step.eta. -/

namespace FX1Poly.Core.Spike

/-- Lift a β/ι-step under the etaLam source context `lam[ app[ weaken _, newestVar ] ]`. -/
theorem etaLamSourceCongruence {scope : Nat}
    {innerFunction reduct : RawTerm scope}
    (betaStep : Step innerFunction reduct) :
    Step (RawTerm.etaLamSource innerFunction) (RawTerm.etaLamSource reduct) :=
  Step.cong .gen_lam ()
    (StepChildren.here .childNil
      (Step.cong .gen_app ()
        (StepChildren.here
          (.childCons RawTerm.newestVar .childNil : RawTermChildren [0] (scope + 1))
          (Step.weaken betaStep))))

/-- etaLam quasi-commutes over β: an etaLam η-step then a β/ι-step reorders into a β/ι-step then βη*. -/
theorem etaLamQuasiCommutesOverBeta {scope : Nat}
    {innerFunction reduct : RawTerm scope}
    (betaStep : Step innerFunction reduct) :
    ∃ commonReduct, Step (RawTerm.etaLamSource innerFunction) commonReduct ∧
      UnionStar Step Step.eta commonReduct reduct :=
  ⟨RawTerm.etaLamSource reduct,
   etaLamSourceCongruence betaStep,
   UnionStar.tailRight (UnionStar.refl _) (Step.eta.etaLam reduct)⟩

end FX1Poly.Core.Spike

#print axioms FX1Poly.Core.Spike.etaLamSourceCongruence
#print axioms FX1Poly.Core.Spike.etaLamQuasiCommutesOverBeta
