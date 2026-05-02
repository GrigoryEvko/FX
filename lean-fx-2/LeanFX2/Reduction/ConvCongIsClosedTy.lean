import LeanFX2.Term.SubjectReductionGeneral
import LeanFX2.Reduction.Conv

/-! # Reduction/ConvCongIsClosedTy — generic Conv cong-rule lifter

The companion to `Term.SubjectReductionGeneral.lean`'s
`StepStar.lift_at_isClosedTy`.  Where the StepStar helper lifts a
chain on a sub-position, this file's `Conv.cong_at_isClosedTy`
lifts a *convertibility* on the sub-position via existential
extraction + SR + re-wrap on both reduction chains.

Together they collapse every "Conv on a sub-term at a closed type
lifts to Conv on the wrapper" rule into a 1-step parameterization.

This file ships:

* `Conv.cong_at_isClosedTy` — Conv-level lifter via existential
  extraction + SR + re-wrap.  Built on top of
  `StepStar.lift_at_isClosedTy` (which lives in
  `SubjectReductionGeneral.lean` since it does not depend on Conv).

* Five worked corollaries: optionSome, eitherInl, eitherInr,
  listCons head/tail.

## The pattern

Every "cong on a sub-position at a closed type" rule has the same
structure: induct on the chain, dispatch refl + step cases, use
`Step.preserves_isClosedTy` in the step case to bridge the
existential intermediate type back to the closed type, then apply
the ctor's Step cong rule + IH.  The variable parts are exactly
the wrapper function and the Step cong ctor; everything else is
boilerplate.

## Audit + zero-axiom

`AuditPhase12A2ConvCongIsClosedTy.lean` verifies both the generic
helpers and a smoke test (a one-line corollary deriving an
existing per-ctor rule).
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- Generic Conv-level cong rule at a closed sub-position.  Extracts
the convertibility's existential common reduct, applies SR to
constrain its type to `closedTy`, then re-wraps via
`StepStar.lift_at_isClosedTy` on both reduction chains. -/
theorem Conv.cong_at_isClosedTy
    {closedTy resultTy : Ty level scope}
    (closedTyIsClosed : IsClosedTy closedTy)
    {wrapRaw : RawTerm scope → RawTerm scope}
    (wrap : ∀ {raw : RawTerm scope}, Term context closedTy raw →
            Term context resultTy (wrapRaw raw))
    (stepWrap : ∀ {sourceRaw targetRaw : RawTerm scope}
                 {sourceTerm : Term context closedTy sourceRaw}
                 {targetTerm : Term context closedTy targetRaw},
                 Step sourceTerm targetTerm →
                 Step (wrap sourceTerm) (wrap targetTerm))
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context closedTy srcRaw}
    {tgtTerm : Term context closedTy tgtRaw}
    (subConv : Conv srcTerm tgtTerm) :
    Conv (wrap srcTerm) (wrap tgtTerm) := by
  obtain ⟨midType, midRaw, midTerm, chainA, chainB⟩ := subConv
  have midIsClosed : midType = closedTy :=
    StepStar.preserves_isClosedTy closedTyIsClosed chainA rfl
  cases midIsClosed
  refine ⟨resultTy, _, wrap midTerm, ?_, ?_⟩
  · exact StepStar.lift_at_isClosedTy
            closedTyIsClosed wrap stepWrap chainA rfl rfl
  · exact StepStar.lift_at_isClosedTy
            closedTyIsClosed wrap stepWrap chainB rfl rfl

/-! ## Worked corollaries via the generic helper

Each is a one-line specialization parameterizing
`Conv.cong_at_isClosedTy` at the matching wrapper + Step cong ctor.

These deliver the parametric-ctor-position cong rules that
`SubjectReductionGeneral.lean`'s closed-type SR specialisations
unblock.  Same call-site signature as a hand-rolled per-ctor
proof; same proof obligations are factored into the generic
helper. -/

/-- Conv cong on `Term.optionSome`'s value position when element
type is closed. -/
theorem Conv.optionSome_value_cong_isClosedTy
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {valueRawA valueRawB : RawTerm scope}
    {valueTermA : Term context elementType valueRawA}
    {valueTermB : Term context elementType valueRawB}
    (valueConv : Conv valueTermA valueTermB) :
    Conv (Term.optionSome valueTermA) (Term.optionSome valueTermB) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.optionType elementType)
    closedElement
    (wrapRaw := RawTerm.optionSome)
    (fun term => Term.optionSome term)
    (fun step => Step.optionSomeValue step)
    valueConv

/-- Conv cong on `Term.eitherInl`'s value position when left type
is closed.  rightType need not be closed. -/
theorem Conv.eitherInl_value_cong_isClosedTy
    {leftType rightType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    {valueRawA valueRawB : RawTerm scope}
    {valueTermA : Term context leftType valueRawA}
    {valueTermB : Term context leftType valueRawB}
    (valueConv : Conv valueTermA valueTermB) :
    Conv (Term.eitherInl (rightType := rightType) valueTermA)
         (Term.eitherInl (rightType := rightType) valueTermB) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.eitherType leftType rightType)
    closedLeft
    (wrapRaw := RawTerm.eitherInl)
    (fun term => Term.eitherInl (rightType := rightType) term)
    (fun step => Step.eitherInlValue step)
    valueConv

/-- Conv cong on `Term.eitherInr`'s value position when right type
is closed.  leftType need not be closed. -/
theorem Conv.eitherInr_value_cong_isClosedTy
    {leftType rightType : Ty level scope}
    (closedRight : IsClosedTy rightType)
    {valueRawA valueRawB : RawTerm scope}
    {valueTermA : Term context rightType valueRawA}
    {valueTermB : Term context rightType valueRawB}
    (valueConv : Conv valueTermA valueTermB) :
    Conv (Term.eitherInr (leftType := leftType) valueTermA)
         (Term.eitherInr (leftType := leftType) valueTermB) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.eitherType leftType rightType)
    closedRight
    (wrapRaw := RawTerm.eitherInr)
    (fun term => Term.eitherInr (leftType := leftType) term)
    (fun step => Step.eitherInrValue step)
    valueConv

/-- Conv cong on `Term.listCons`'s head position with a fixed tail
when element type is closed. -/
theorem Conv.listCons_head_cong_isClosedTy
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {tailRaw : RawTerm scope}
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    {headRawA headRawB : RawTerm scope}
    {headTermA : Term context elementType headRawA}
    {headTermB : Term context elementType headRawB}
    (headConv : Conv headTermA headTermB) :
    Conv (Term.listCons headTermA tailTerm)
         (Term.listCons headTermB tailTerm) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.listType elementType)
    closedElement
    (wrapRaw := fun raw => RawTerm.listCons raw tailRaw)
    (fun term => Term.listCons term tailTerm)
    (fun step => Step.listConsHead step)
    headConv

/-- Conv cong on `Term.listCons`'s tail position with a fixed head
when element type is closed. -/
theorem Conv.listCons_tail_cong_isClosedTy
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {headRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    {tailRawA tailRawB : RawTerm scope}
    {tailTermA : Term context (Ty.listType elementType) tailRawA}
    {tailTermB : Term context (Ty.listType elementType) tailRawB}
    (tailConv : Conv tailTermA tailTermB) :
    Conv (Term.listCons headTerm tailTermA)
         (Term.listCons headTerm tailTermB) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.listType elementType)
    (IsClosedTy.listType closedElement)
    (wrapRaw := fun raw => RawTerm.listCons headRaw raw)
    (fun term => Term.listCons headTerm term)
    (fun step => Step.listConsTail step)
    tailConv

/-! ## Eliminator scrutinee cong rules

For each list/option/either eliminator, when the element/component
types are closed, Conv on the scrutinee lifts to Conv on the
eliminator wrapper.  Same parameterization template; the
eliminator's branches and motive are fixed. -/

/-- Conv cong on `Term.listElim`'s scrutinee position when element
type is closed. -/
theorem Conv.listElim_scrutinee_cong_isClosedTy
    {elementType motiveType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {scrutRawA scrutRawB nilRaw consRaw : RawTerm scope}
    {scrutA : Term context (Ty.listType elementType) scrutRawA}
    {scrutB : Term context (Ty.listType elementType) scrutRawB}
    (nilBranch : Term context motiveType nilRaw)
    (consBranch : Term context (Ty.arrow elementType
                                  (Ty.arrow (Ty.listType elementType) motiveType))
                                consRaw)
    (scrutConv : Conv scrutA scrutB) :
    Conv (Term.listElim scrutA nilBranch consBranch)
         (Term.listElim scrutB nilBranch consBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.listType closedElement)
    (wrapRaw := fun raw => RawTerm.listElim raw nilRaw consRaw)
    (fun term => Term.listElim term nilBranch consBranch)
    (fun step => Step.listElimScrutinee step)
    scrutConv

/-- Conv cong on `Term.optionMatch`'s scrutinee position when
element type is closed. -/
theorem Conv.optionMatch_scrutinee_cong_isClosedTy
    {elementType motiveType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {scrutRawA scrutRawB noneRaw someRaw : RawTerm scope}
    {scrutA : Term context (Ty.optionType elementType) scrutRawA}
    {scrutB : Term context (Ty.optionType elementType) scrutRawB}
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (scrutConv : Conv scrutA scrutB) :
    Conv (Term.optionMatch scrutA noneBranch someBranch)
         (Term.optionMatch scrutB noneBranch someBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.optionType closedElement)
    (wrapRaw := fun raw => RawTerm.optionMatch raw noneRaw someRaw)
    (fun term => Term.optionMatch term noneBranch someBranch)
    (fun step => Step.optionMatchScrutinee step)
    scrutConv

/-- Conv cong on `Term.eitherMatch`'s scrutinee position when both
component types are closed. -/
theorem Conv.eitherMatch_scrutinee_cong_isClosedTy
    {leftType rightType motiveType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    (closedRight : IsClosedTy rightType)
    {scrutRawA scrutRawB leftRaw rightRaw : RawTerm scope}
    {scrutA : Term context (Ty.eitherType leftType rightType) scrutRawA}
    {scrutB : Term context (Ty.eitherType leftType rightType) scrutRawB}
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (scrutConv : Conv scrutA scrutB) :
    Conv (Term.eitherMatch scrutA leftBranch rightBranch)
         (Term.eitherMatch scrutB leftBranch rightBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.eitherType closedLeft closedRight)
    (wrapRaw := fun raw => RawTerm.eitherMatch raw leftRaw rightRaw)
    (fun term => Term.eitherMatch term leftBranch rightBranch)
    (fun step => Step.eitherMatchScrutinee step)
    scrutConv

end LeanFX2
