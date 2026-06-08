import FX1Poly.Core.StrongNormalizationUnion
import FX1Poly.Core.StepEta
import FX1Poly.Core.StepSubst

/-! Probe (NEVER committed): OSN-B5 — etaPathLam (binder, etaLam pattern) + etaGlueIntro (duplicating, etaPair pattern). -/

namespace FX1Poly.Core.Spike

/-- etaPathLam source congruence — etaLam's shape over gen_pathLam/gen_pathApp. -/
theorem etaPathLamSourceCongruence {scope : Nat}
    {innerPath reduct : RawTerm scope}
    (betaStep : Step innerPath reduct) :
    Step (RawTerm.etaPathLamSource innerPath) (RawTerm.etaPathLamSource reduct) :=
  Step.cong .gen_pathLam ()
    (StepChildren.here .childNil
      (Step.cong .gen_pathApp ()
        (StepChildren.here
          (.childCons RawTerm.newestVar .childNil : RawTermChildren [0] (scope + 1))
          (Step.weaken betaStep))))

theorem etaPathLamQuasiCommutesOverBeta {scope : Nat}
    {innerPath reduct : RawTerm scope}
    (betaStep : Step innerPath reduct) :
    ∃ commonReduct, Step (RawTerm.etaPathLamSource innerPath) commonReduct ∧
      UnionStar Step Step.eta commonReduct reduct :=
  ⟨RawTerm.etaPathLamSource reduct,
   etaPathLamSourceCongruence betaStep,
   UnionStar.tailRight (UnionStar.refl _) (Step.eta.etaPathLam reduct)⟩

/-- etaGlueIntro reduce the `glueElim g` copy (child 0). -/
theorem etaGlueIntroReduceElim {scope : Nat}
    {gluedTerm reduct : RawTerm scope}
    (betaStep : Step gluedTerm reduct) :
    Step (RawTerm.etaGlueIntroSource gluedTerm)
      (.mkGen .gen_glueIntro ()
        (.childCons (.mkGen .gen_glueElim () (.childCons reduct .childNil))
          (.childCons gluedTerm .childNil))) :=
  Step.cong .gen_glueIntro ()
    (StepChildren.here _
      (Step.cong .gen_glueElim () (StepChildren.here .childNil betaStep)))

/-- etaGlueIntro reduce the direct second `g` copy (child 1), reaching `etaGlueIntroSource reduct`. -/
theorem etaGlueIntroReduceSecond {scope : Nat}
    {gluedTerm reduct : RawTerm scope}
    (betaStep : Step gluedTerm reduct) :
    Step
      (.mkGen .gen_glueIntro ()
        (.childCons (.mkGen .gen_glueElim () (.childCons reduct .childNil))
          (.childCons gluedTerm .childNil)))
      (RawTerm.etaGlueIntroSource reduct) :=
  Step.cong .gen_glueIntro ()
    (StepChildren.there _
      (StepChildren.here .childNil betaStep))

theorem etaGlueIntroQuasiCommutesOverBeta {scope : Nat}
    {gluedTerm reduct : RawTerm scope}
    (betaStep : Step gluedTerm reduct) :
    ∃ commonReduct, Step (RawTerm.etaGlueIntroSource gluedTerm) commonReduct ∧
      UnionStar Step Step.eta commonReduct reduct :=
  ⟨_,
   etaGlueIntroReduceElim betaStep,
   UnionStar.tailRight
     (UnionStar.tailLeft (UnionStar.refl _) (etaGlueIntroReduceSecond betaStep))
     (Step.eta.etaGlueIntro reduct)⟩

end FX1Poly.Core.Spike

#print axioms FX1Poly.Core.Spike.etaPathLamQuasiCommutesOverBeta
#print axioms FX1Poly.Core.Spike.etaGlueIntroQuasiCommutesOverBeta
