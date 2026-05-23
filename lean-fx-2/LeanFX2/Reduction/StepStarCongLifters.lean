import LeanFX2.Term.SubjectReductionGeneral

/-! # Reduction/StepStarCongLifters — closed-type congruence lifters
for the single-step reflexive-transitive closure.

Each lemma lifts a `StepStar` chain on ONE sub-position whose type is
closed (`IsClosedTy`) into a `StepStar` chain on the wrapped term, by
composing the matching single-step `Step` congruence constructor
across the chain.

## Why closedness is required

A single `Step` congruence constructor (`Step.optionSomeValue`,
`Step.listConsHead`, ...) requires its inner source and target at the
SAME type.  Inside a `StepStar` chain the intermediate types can in
principle drift, so lifting needs subject reduction to pin the chain
at its starting type.  The general subject-reduction theorem
`Step.preserves_isClosedTy` (Term/SubjectReductionGeneral) holds
exactly at closed types, so each lifter carries an `IsClosedTy`
witness for the reducing position's type.  This matches the existing
`StepStar.{natSucc, boolElimScrutinee, natElimScrutinee,
natRecScrutinee}_lift` family — the lemmas here extend that family to
the value constructors (`optionSome`, `listCons`, `eitherInl`,
`eitherInr`) and the remaining parametric eliminator scrutinees
(`listElim`, `optionMatch`, `eitherMatch`).

## Workhorse

Every lemma is a one-step specialization of
`StepStar.lift_at_isClosedTy`, parameterized at the matching wrapper
Term function and `Step` congruence constructor.  The `_general`
flavor takes free `srcTy = closedTy` / `tgtTy = closedTy` equalities
so the chain induction runs before the type is baked into the wrapped
term; the headline flavor supplies `rfl rfl`.

## Downstream

These cong-lifters are the single-position building blocks behind the
`Conv.*_cong` family and behind `Step.par.toStepStar` (parallel
reduction ⊆ single-step RT closure).  An N-ary parallel-step
congruence composes per-position lifters via `StepStar.append`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-! ## Option value -/

/-- Generalized lift for `optionSome` value cong.  One-step
parameterization of `StepStar.lift_at_isClosedTy`. -/
theorem StepStar.optionSomeValue_lift_general
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsElement : srcTy = elementType)
    (tgtIsElement : tgtTy = elementType) :
    StepStar (Term.optionSome (srcIsElement ▸ srcTerm))
             (Term.optionSome (tgtIsElement ▸ tgtTerm)) :=
  StepStar.lift_at_isClosedTy
    (resultTy := Ty.optionType elementType) closedElement
    (wrapRaw := RawTerm.optionSome)
    (fun term => Term.optionSome term)
    (fun step => Step.optionSomeValue step)
    someChain srcIsElement tgtIsElement

/-- Lift a `StepStar` chain between element-typed terms to a
`StepStar` chain between `optionSome`-wrappers, when the element type
is closed. -/
theorem StepStar.optionSomeValue_lift
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {valueRawA valueRawB : RawTerm scope}
    {valueA : Term context elementType valueRawA}
    {valueB : Term context elementType valueRawB}
    (chain : StepStar valueA valueB) :
    StepStar (Term.optionSome valueA) (Term.optionSome valueB) :=
  StepStar.optionSomeValue_lift_general closedElement chain rfl rfl

/-! ## Either values -/

/-- Generalized lift for `eitherInl` value cong. -/
theorem StepStar.eitherInlValue_lift_general
    {leftType rightType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsLeft : srcTy = leftType)
    (tgtIsLeft : tgtTy = leftType) :
    StepStar (Term.eitherInl (rightType := rightType) (srcIsLeft ▸ srcTerm))
             (Term.eitherInl (rightType := rightType) (tgtIsLeft ▸ tgtTerm)) :=
  StepStar.lift_at_isClosedTy
    (resultTy := Ty.eitherType leftType rightType) closedLeft
    (wrapRaw := RawTerm.eitherInl)
    (fun term => Term.eitherInl (rightType := rightType) term)
    (fun step => Step.eitherInlValue step)
    someChain srcIsLeft tgtIsLeft

/-- Lift a `StepStar` chain between left-typed terms to a `StepStar`
chain between `eitherInl`-wrappers, when the left type is closed.  The
right type need not be closed. -/
theorem StepStar.eitherInlValue_lift
    {leftType rightType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    {valueRawA valueRawB : RawTerm scope}
    {valueA : Term context leftType valueRawA}
    {valueB : Term context leftType valueRawB}
    (chain : StepStar valueA valueB) :
    StepStar (Term.eitherInl (rightType := rightType) valueA)
             (Term.eitherInl (rightType := rightType) valueB) :=
  StepStar.eitherInlValue_lift_general closedLeft chain rfl rfl

/-- Generalized lift for `eitherInr` value cong. -/
theorem StepStar.eitherInrValue_lift_general
    {leftType rightType : Ty level scope}
    (closedRight : IsClosedTy rightType)
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsRight : srcTy = rightType)
    (tgtIsRight : tgtTy = rightType) :
    StepStar (Term.eitherInr (leftType := leftType) (srcIsRight ▸ srcTerm))
             (Term.eitherInr (leftType := leftType) (tgtIsRight ▸ tgtTerm)) :=
  StepStar.lift_at_isClosedTy
    (resultTy := Ty.eitherType leftType rightType) closedRight
    (wrapRaw := RawTerm.eitherInr)
    (fun term => Term.eitherInr (leftType := leftType) term)
    (fun step => Step.eitherInrValue step)
    someChain srcIsRight tgtIsRight

/-- Lift a `StepStar` chain between right-typed terms to a `StepStar`
chain between `eitherInr`-wrappers, when the right type is closed.
The left type need not be closed. -/
theorem StepStar.eitherInrValue_lift
    {leftType rightType : Ty level scope}
    (closedRight : IsClosedTy rightType)
    {valueRawA valueRawB : RawTerm scope}
    {valueA : Term context rightType valueRawA}
    {valueB : Term context rightType valueRawB}
    (chain : StepStar valueA valueB) :
    StepStar (Term.eitherInr (leftType := leftType) valueA)
             (Term.eitherInr (leftType := leftType) valueB) :=
  StepStar.eitherInrValue_lift_general closedRight chain rfl rfl

/-! ## List cons -/

/-- Generalized lift for `listCons` head cong, holding the tail
fixed. -/
theorem StepStar.listConsHead_lift_general
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsElement : srcTy = elementType)
    (tgtIsElement : tgtTy = elementType)
    {tailRaw : RawTerm scope}
    (tailTerm : Term context (Ty.listType elementType) tailRaw) :
    StepStar (Term.listCons (srcIsElement ▸ srcTerm) tailTerm)
             (Term.listCons (tgtIsElement ▸ tgtTerm) tailTerm) :=
  StepStar.lift_at_isClosedTy
    (resultTy := Ty.listType elementType) closedElement
    (wrapRaw := fun raw => RawTerm.listCons raw tailRaw)
    (fun term => Term.listCons term tailTerm)
    (fun step => Step.listConsHead step)
    someChain srcIsElement tgtIsElement

/-- Lift a `StepStar` chain on the head of `Term.listCons` to a
`StepStar` chain on the cons, holding the tail fixed, when the element
type is closed. -/
theorem StepStar.listConsHead_lift
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {headRawA headRawB tailRaw : RawTerm scope}
    {headA : Term context elementType headRawA}
    {headB : Term context elementType headRawB}
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (chain : StepStar headA headB) :
    StepStar (Term.listCons headA tailTerm) (Term.listCons headB tailTerm) :=
  StepStar.listConsHead_lift_general closedElement chain rfl rfl tailTerm

/-- Generalized lift for `listCons` tail cong, holding the head
fixed. -/
theorem StepStar.listConsTail_lift_general
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsList : srcTy = Ty.listType elementType)
    (tgtIsList : tgtTy = Ty.listType elementType)
    {headRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw) :
    StepStar (Term.listCons headTerm (srcIsList ▸ srcTerm))
             (Term.listCons headTerm (tgtIsList ▸ tgtTerm)) :=
  StepStar.lift_at_isClosedTy
    (resultTy := Ty.listType elementType) (IsClosedTy.listType closedElement)
    (wrapRaw := fun raw => RawTerm.listCons headRaw raw)
    (fun term => Term.listCons headTerm term)
    (fun step => Step.listConsTail step)
    someChain srcIsList tgtIsList

/-- Lift a `StepStar` chain on the tail of `Term.listCons` to a
`StepStar` chain on the cons, holding the head fixed, when the element
type is closed. -/
theorem StepStar.listConsTail_lift
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {headRaw tailRawA tailRawB : RawTerm scope}
    {tailA : Term context (Ty.listType elementType) tailRawA}
    {tailB : Term context (Ty.listType elementType) tailRawB}
    (headTerm : Term context elementType headRaw)
    (chain : StepStar tailA tailB) :
    StepStar (Term.listCons headTerm tailA) (Term.listCons headTerm tailB) :=
  StepStar.listConsTail_lift_general closedElement chain rfl rfl headTerm

/-! ## Parametric eliminator scrutinees -/

/-- Generalized lift for `listElim` scrutinee cong. -/
theorem StepStar.listElimScrutinee_lift_general
    {elementType motiveType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsList : srcTy = Ty.listType elementType)
    (tgtIsList : tgtTy = Ty.listType elementType)
    {nilRaw consRaw : RawTerm scope}
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    StepStar (Term.listElim (srcIsList ▸ srcTerm) nilBranch consBranch)
             (Term.listElim (tgtIsList ▸ tgtTerm) nilBranch consBranch) :=
  StepStar.lift_at_isClosedTy
    (resultTy := motiveType) (IsClosedTy.listType closedElement)
    (wrapRaw := fun raw => RawTerm.listElim raw nilRaw consRaw)
    (fun term => Term.listElim term nilBranch consBranch)
    (fun step => Step.listElimScrutinee step)
    someChain srcIsList tgtIsList

/-- Lift a `StepStar` chain between list-typed scrutinees to a
`StepStar` chain between `listElim`-wrappers, when the element type is
closed. -/
theorem StepStar.listElimScrutinee_lift
    {elementType motiveType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {scrutRawA scrutRawB : RawTerm scope}
    {scrutA : Term context (Ty.listType elementType) scrutRawA}
    {scrutB : Term context (Ty.listType elementType) scrutRawB}
    (chain : StepStar scrutA scrutB)
    {nilRaw consRaw : RawTerm scope}
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    StepStar (Term.listElim scrutA nilBranch consBranch)
             (Term.listElim scrutB nilBranch consBranch) :=
  StepStar.listElimScrutinee_lift_general closedElement chain rfl rfl
    nilBranch consBranch

/-- Generalized lift for `optionMatch` scrutinee cong. -/
theorem StepStar.optionMatchScrutinee_lift_general
    {elementType motiveType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsOption : srcTy = Ty.optionType elementType)
    (tgtIsOption : tgtTy = Ty.optionType elementType)
    {noneRaw someRaw : RawTerm scope}
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    StepStar (Term.optionMatch (srcIsOption ▸ srcTerm) noneBranch someBranch)
             (Term.optionMatch (tgtIsOption ▸ tgtTerm) noneBranch someBranch) :=
  StepStar.lift_at_isClosedTy
    (resultTy := motiveType) (IsClosedTy.optionType closedElement)
    (wrapRaw := fun raw => RawTerm.optionMatch raw noneRaw someRaw)
    (fun term => Term.optionMatch term noneBranch someBranch)
    (fun step => Step.optionMatchScrutinee step)
    someChain srcIsOption tgtIsOption

/-- Lift a `StepStar` chain between option-typed scrutinees to a
`StepStar` chain between `optionMatch`-wrappers, when the element type
is closed. -/
theorem StepStar.optionMatchScrutinee_lift
    {elementType motiveType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {scrutRawA scrutRawB : RawTerm scope}
    {scrutA : Term context (Ty.optionType elementType) scrutRawA}
    {scrutB : Term context (Ty.optionType elementType) scrutRawB}
    (chain : StepStar scrutA scrutB)
    {noneRaw someRaw : RawTerm scope}
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    StepStar (Term.optionMatch scrutA noneBranch someBranch)
             (Term.optionMatch scrutB noneBranch someBranch) :=
  StepStar.optionMatchScrutinee_lift_general closedElement chain rfl rfl
    noneBranch someBranch

/-- Generalized lift for `eitherMatch` scrutinee cong. -/
theorem StepStar.eitherMatchScrutinee_lift_general
    {leftType rightType motiveType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    (closedRight : IsClosedTy rightType)
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsEither : srcTy = Ty.eitherType leftType rightType)
    (tgtIsEither : tgtTy = Ty.eitherType leftType rightType)
    {leftRaw rightRaw : RawTerm scope}
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    StepStar (Term.eitherMatch (srcIsEither ▸ srcTerm) leftBranch rightBranch)
             (Term.eitherMatch (tgtIsEither ▸ tgtTerm) leftBranch rightBranch) :=
  StepStar.lift_at_isClosedTy
    (resultTy := motiveType) (IsClosedTy.eitherType closedLeft closedRight)
    (wrapRaw := fun raw => RawTerm.eitherMatch raw leftRaw rightRaw)
    (fun term => Term.eitherMatch term leftBranch rightBranch)
    (fun step => Step.eitherMatchScrutinee step)
    someChain srcIsEither tgtIsEither

/-- Lift a `StepStar` chain between either-typed scrutinees to a
`StepStar` chain between `eitherMatch`-wrappers, when both component
types are closed. -/
theorem StepStar.eitherMatchScrutinee_lift
    {leftType rightType motiveType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    (closedRight : IsClosedTy rightType)
    {scrutRawA scrutRawB : RawTerm scope}
    {scrutA : Term context (Ty.eitherType leftType rightType) scrutRawA}
    {scrutB : Term context (Ty.eitherType leftType rightType) scrutRawB}
    (chain : StepStar scrutA scrutB)
    {leftRaw rightRaw : RawTerm scope}
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    StepStar (Term.eitherMatch scrutA leftBranch rightBranch)
             (Term.eitherMatch scrutB leftBranch rightBranch) :=
  StepStar.eitherMatchScrutinee_lift_general closedLeft closedRight chain rfl rfl
    leftBranch rightBranch

end LeanFX2
