import FX1Poly.Core.StrongNormalizationUnion
import FX1Poly.Core.StepEta
import FX1Poly.Core.StepSubst

/-! Probe (NEVER committed): OSN-B4 — etaModIntro (single strip) + etaPair (duplicating) postponement. -/

namespace FX1Poly.Core.Spike

/-- etaModIntro source congruence: a β/ι-step lifts through `modIntro[ modElim[ _ ] ]` (no binder/weaken). -/
theorem etaModIntroSourceCongruence {scope : Nat}
    {modalTerm reduct : RawTerm scope}
    (betaStep : Step modalTerm reduct) :
    Step (RawTerm.etaModIntroSource modalTerm) (RawTerm.etaModIntroSource reduct) :=
  Step.cong .gen_modIntro ()
    (StepChildren.here .childNil
      (Step.cong .gen_modElim ()
        (StepChildren.here .childNil betaStep)))

theorem etaModIntroQuasiCommutesOverBeta {scope : Nat}
    {modalTerm reduct : RawTerm scope}
    (betaStep : Step modalTerm reduct) :
    ∃ commonReduct, Step (RawTerm.etaModIntroSource modalTerm) commonReduct ∧
      UnionStar Step Step.eta commonReduct reduct :=
  ⟨RawTerm.etaModIntroSource reduct,
   etaModIntroSourceCongruence betaStep,
   UnionStar.tailRight (UnionStar.refl _) (Step.eta.etaModIntro reduct)⟩

/-- etaPair reduce-fst: step the `fst p` copy inside `pair[ fst p, snd p ]`. -/
theorem etaPairSourceReduceFst {scope : Nat}
    {pairTerm reduct : RawTerm scope}
    (betaStep : Step pairTerm reduct) :
    Step (RawTerm.etaPairSource pairTerm)
      (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_fst () (.childCons reduct .childNil))
          (.childCons (.mkGen .gen_snd () (.childCons pairTerm .childNil)) .childNil))) :=
  Step.cong .gen_pair ()
    (StepChildren.here _
      (Step.cong .gen_fst () (StepChildren.here .childNil betaStep)))

/-- etaPair reduce-snd: step the `snd p` copy, with `fst` already at the reduct. -/
theorem etaPairSourceReduceSnd {scope : Nat}
    {pairTerm reduct : RawTerm scope}
    (betaStep : Step pairTerm reduct) :
    Step
      (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_fst () (.childCons reduct .childNil))
          (.childCons (.mkGen .gen_snd () (.childCons pairTerm .childNil)) .childNil)))
      (RawTerm.etaPairSource reduct) :=
  Step.cong .gen_pair ()
    (StepChildren.there _
      (StepChildren.here .childNil
        (Step.cong .gen_snd () (StepChildren.here .childNil betaStep))))

theorem etaPairQuasiCommutesOverBeta {scope : Nat}
    {pairTerm reduct : RawTerm scope}
    (betaStep : Step pairTerm reduct) :
    ∃ commonReduct, Step (RawTerm.etaPairSource pairTerm) commonReduct ∧
      UnionStar Step Step.eta commonReduct reduct :=
  ⟨_,
   etaPairSourceReduceFst betaStep,
   UnionStar.tailRight
     (UnionStar.tailLeft (UnionStar.refl _) (etaPairSourceReduceSnd betaStep))
     (Step.eta.etaPair reduct)⟩

end FX1Poly.Core.Spike

#print axioms FX1Poly.Core.Spike.etaModIntroQuasiCommutesOverBeta
#print axioms FX1Poly.Core.Spike.etaPairQuasiCommutesOverBeta
