import FX1Poly.Typed.TypedChurchNumeralAddition

namespace FX1Poly.Typed
open FX1Poly.Core StepStar

-- The multiplicative induction: iterating the n-fold step (n A f) outer-many times = f^(outer*n) x.
theorem churchMultiplicationStepIterate (countOuter countInner : Nat)
    (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (iteratedApplication countOuter
        (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF) baseX)
      (iteratedApplication (countOuter * countInner) handlerF baseX) := by
  induction countOuter with
  | zero =>
      rw [Nat.zero_mul]
      exact StepStar.refl _
  | succ priorOuter priorIH =>
      have liftIH : StepStar
          (appCell (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF)
            (iteratedApplication priorOuter
              (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF) baseX))
          (appCell (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF)
            (iteratedApplication (priorOuter * countInner) handlerF baseX)) :=
        StepStar.congAt
          (fun hole =>
            appCell (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF) hole)
          (fun argStep => Step.appArgCong _ argStep)
          priorIH
      have applyN : StepStar
          (appCell (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF)
            (iteratedApplication (priorOuter * countInner) handlerF baseX))
          (iteratedApplication countInner handlerF
            (iteratedApplication (priorOuter * countInner) handlerF baseX)) :=
        churchNumeral_appliedReducesToIterate_general countInner typeA handlerF
          (iteratedApplication (priorOuter * countInner) handlerF baseX)
      have combine : iteratedApplication countInner handlerF
            (iteratedApplication (priorOuter * countInner) handlerF baseX)
          = iteratedApplication ((priorOuter + 1) * countInner) handlerF baseX := by
        rw [← iteratedApplication_add countInner (priorOuter * countInner) handlerF baseX,
          Nat.succ_mul, Nat.add_comm countInner (priorOuter * countInner)]
      show StepStar
        (appCell (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF)
          (iteratedApplication priorOuter
            (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF) baseX)) _
      exact combine ▸ StepStar.trans_compose liftIH applyN

-- The Church-multiplication body computes f^(m*n) x for general m,n and symbolic A,f,x.
theorem churchMultiplicationBodyComputes (countLeft countRight : Nat)
    (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA)
        (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF)) baseX)
      (iteratedApplication (countLeft * countRight) handlerF baseX) := by
  have outerReduces : StepStar
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA)
        (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF)) baseX)
      (iteratedApplication countLeft
        (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX) :=
    churchNumeral_appliedReducesToIterate_general countLeft typeA
      (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX
  exact StepStar.trans_compose outerReduces
    (churchMultiplicationStepIterate countLeft countRight typeA handlerF baseX)

-- Concrete smoke: 2 * 3 computes f^6 x.
theorem churchTwoTimesThreeComputes (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (appCell (appCell (appCell (churchNumeralLambda 2) typeA)
        (appCell (appCell (churchNumeralLambda 3) typeA) handlerF)) baseX)
      (iteratedApplication 6 handlerF baseX) :=
  churchMultiplicationBodyComputes 2 3 typeA handlerF baseX

end FX1Poly.Typed

#print axioms FX1Poly.Typed.churchMultiplicationStepIterate
#print axioms FX1Poly.Typed.churchMultiplicationBodyComputes
#print axioms FX1Poly.Typed.churchTwoTimesThreeComputes
