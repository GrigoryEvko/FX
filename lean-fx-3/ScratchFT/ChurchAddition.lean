import FX1Poly.Typed.TypedChurchNumeralComputeGeneral

namespace FX1Poly.Typed
open FX1Poly.Core StepStar

-- 1. Arithmetic heart: f^(m+n) x = f^m (f^n x).
theorem iteratedApplication_add {scope : Nat} (countLeft countRight : Nat)
    (stepFn base : RawTerm scope) :
    iteratedApplication (countLeft + countRight) stepFn base
      = iteratedApplication countLeft stepFn (iteratedApplication countRight stepFn base) := by
  induction countLeft with
  | zero =>
      show iteratedApplication (0 + countRight) stepFn base = iteratedApplication countRight stepFn base
      rw [Nat.zero_add]
  | succ priorLeft priorIH =>
      rw [Nat.succ_add]
      show appCell stepFn (iteratedApplication (priorLeft + countRight) stepFn base)
        = appCell stepFn (iteratedApplication priorLeft stepFn (iteratedApplication countRight stepFn base))
      rw [priorIH]

-- 2. The argument-position single-step congruence for an application cell.
theorem Step.appArgCong {scope : Nat} (func : RawTerm scope) {arg arg' : RawTerm scope}
    (argStep : Step arg arg') : Step (appCell func arg) (appCell func arg') :=
  Step.cong .gen_app ()
    (StepChildren.there (parentScope := scope) (headShift := 0) func
      (StepChildren.here (parentScope := scope) (headShift := 0) (restShifts := []) .childNil argStep))

-- 3. The Church-addition body computes f^(m+n) x for general m,n and symbolic A,f,x.
theorem churchAdditionBodyComputes (countLeft countRight : Nat) (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (appCell (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX))
      (iteratedApplication (countLeft + countRight) handlerF baseX) := by
  have innerReduces : StepStar
      (appCell (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX)
      (iteratedApplication countRight handlerF baseX) :=
    churchNumeral_appliedReducesToIterate_general countRight typeA handlerF baseX
  have liftedInner : StepStar
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (appCell (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX))
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (iteratedApplication countRight handlerF baseX)) :=
    StepStar.congAt
      (fun hole => appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF) hole)
      (fun argStep => Step.appArgCong _ argStep)
      innerReduces
  have outerReduces : StepStar
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (iteratedApplication countRight handlerF baseX))
      (iteratedApplication countLeft handlerF (iteratedApplication countRight handlerF baseX)) :=
    churchNumeral_appliedReducesToIterate_general countLeft typeA handlerF
      (iteratedApplication countRight handlerF baseX)
  have combine : iteratedApplication countLeft handlerF (iteratedApplication countRight handlerF baseX)
      = iteratedApplication (countLeft + countRight) handlerF baseX :=
    (iteratedApplication_add countLeft countRight handlerF baseX).symm
  exact combine ▸ StepStar.trans_compose liftedInner outerReduces

-- 4. Concrete smoke: 2 + 3 computes f^5 x.
theorem churchTwoPlusThreeComputes (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (appCell (appCell (appCell (churchNumeralLambda 2) typeA) handlerF)
        (appCell (appCell (appCell (churchNumeralLambda 3) typeA) handlerF) baseX))
      (iteratedApplication 5 handlerF baseX) :=
  churchAdditionBodyComputes 2 3 typeA handlerF baseX

end FX1Poly.Typed

#print axioms FX1Poly.Typed.iteratedApplication_add
#print axioms FX1Poly.Typed.Step.appArgCong
#print axioms FX1Poly.Typed.churchAdditionBodyComputes
#print axioms FX1Poly.Typed.churchTwoPlusThreeComputes
