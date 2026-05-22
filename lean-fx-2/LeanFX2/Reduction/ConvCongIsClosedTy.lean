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

/-! ## Binary lifter — two closed sub-positions

`Conv.cong2_at_isClosedTy` generalises `cong_at_isClosedTy` to a
binary wrapper.  Each sub-position has its own (possibly distinct)
closed type, its own SR-applicable existential extraction, and its
own per-position Step cong rule.  Internally we compose two
applications of `StepStar.lift_at_isClosedTy` via
`StepStar.append`: first vary the left position keeping the right
fixed at the source raw, then vary the right keeping the left
fixed at its mid reduct.  No `Conv.trans` required (CONVTRANS-D
#1735 is still pending). -/

/-- Generic 2-arg Conv-level cong rule at two closed sub-positions.
Composes via `StepStar.append` + per-position
`StepStar.lift_at_isClosedTy`. -/
theorem Conv.cong2_at_isClosedTy
    {leftClosedTy rightClosedTy resultTy : Ty level scope}
    (leftIsClosed : IsClosedTy leftClosedTy)
    (rightIsClosed : IsClosedTy rightClosedTy)
    {wrapRaw : RawTerm scope → RawTerm scope → RawTerm scope}
    (wrap : ∀ {leftRaw rightRaw : RawTerm scope},
            Term context leftClosedTy leftRaw →
            Term context rightClosedTy rightRaw →
            Term context resultTy (wrapRaw leftRaw rightRaw))
    (stepWrapLeft :
      ∀ {leftSourceRaw leftTargetRaw rightRaw : RawTerm scope}
        {leftSourceTerm : Term context leftClosedTy leftSourceRaw}
        {leftTargetTerm : Term context leftClosedTy leftTargetRaw}
        {rightTerm : Term context rightClosedTy rightRaw},
        Step leftSourceTerm leftTargetTerm →
        Step (wrap leftSourceTerm rightTerm)
             (wrap leftTargetTerm rightTerm))
    (stepWrapRight :
      ∀ {leftRaw rightSourceRaw rightTargetRaw : RawTerm scope}
        {leftTerm : Term context leftClosedTy leftRaw}
        {rightSourceTerm : Term context rightClosedTy rightSourceRaw}
        {rightTargetTerm : Term context rightClosedTy rightTargetRaw},
        Step rightSourceTerm rightTargetTerm →
        Step (wrap leftTerm rightSourceTerm)
             (wrap leftTerm rightTargetTerm))
    {leftSrcRaw leftTgtRaw rightSrcRaw rightTgtRaw : RawTerm scope}
    {leftSrcTerm : Term context leftClosedTy leftSrcRaw}
    {leftTgtTerm : Term context leftClosedTy leftTgtRaw}
    {rightSrcTerm : Term context rightClosedTy rightSrcRaw}
    {rightTgtTerm : Term context rightClosedTy rightTgtRaw}
    (leftConv : Conv leftSrcTerm leftTgtTerm)
    (rightConv : Conv rightSrcTerm rightTgtTerm) :
    Conv (wrap leftSrcTerm rightSrcTerm)
         (wrap leftTgtTerm rightTgtTerm) := by
  obtain ⟨midLeftType, midLeftRaw, midLeftTerm,
          leftChainA, leftChainB⟩ := leftConv
  obtain ⟨midRightType, midRightRaw, midRightTerm,
          rightChainA, rightChainB⟩ := rightConv
  have midLeftIsClosed : midLeftType = leftClosedTy :=
    StepStar.preserves_isClosedTy leftIsClosed leftChainA rfl
  have midRightIsClosed : midRightType = rightClosedTy :=
    StepStar.preserves_isClosedTy rightIsClosed rightChainA rfl
  cases midLeftIsClosed
  cases midRightIsClosed
  refine ⟨resultTy, _, wrap midLeftTerm midRightTerm, ?_, ?_⟩
  · have leftVariation :
        StepStar (wrap leftSrcTerm rightSrcTerm)
                 (wrap midLeftTerm rightSrcTerm) :=
      StepStar.lift_at_isClosedTy
        leftIsClosed
        (fun leftTerm => wrap leftTerm rightSrcTerm)
        (fun stepLeft => stepWrapLeft stepLeft)
        leftChainA rfl rfl
    have rightVariation :
        StepStar (wrap midLeftTerm rightSrcTerm)
                 (wrap midLeftTerm midRightTerm) :=
      StepStar.lift_at_isClosedTy
        rightIsClosed
        (fun rightTerm => wrap midLeftTerm rightTerm)
        (fun stepRight => stepWrapRight stepRight)
        rightChainA rfl rfl
    exact StepStar.append leftVariation rightVariation
  · have leftVariation :
        StepStar (wrap leftTgtTerm rightTgtTerm)
                 (wrap midLeftTerm rightTgtTerm) :=
      StepStar.lift_at_isClosedTy
        leftIsClosed
        (fun leftTerm => wrap leftTerm rightTgtTerm)
        (fun stepLeft => stepWrapLeft stepLeft)
        leftChainB rfl rfl
    have rightVariation :
        StepStar (wrap midLeftTerm rightTgtTerm)
                 (wrap midLeftTerm midRightTerm) :=
      StepStar.lift_at_isClosedTy
        rightIsClosed
        (fun rightTerm => wrap midLeftTerm rightTerm)
        (fun stepRight => stepWrapRight stepRight)
        rightChainB rfl rfl
    exact StepStar.append leftVariation rightVariation

/-! ## Worked corollaries via the generic helper

Each is a one-line specialization parameterizing
`Conv.cong_at_isClosedTy` at the matching wrapper + Step cong ctor.

These deliver the parametric-ctor-position cong rules that
`SubjectReductionGeneral.lean`'s closed-type SR specialisations
unblock.  Same call-site signature as a hand-rolled per-ctor
proof; same proof obligations are factored into the generic
helper. -/

/-- Conv cong on `Term.optionSome`'s value position when element
type is closed.

Named `Conv.optionSome_cong` (term-ctor perspective) so the
`#assert_conv_cong_coverage_budget` gate's exact-name matcher
recognises this as the `Term.optionSome` cong mirror. -/
theorem Conv.optionSome_cong
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
is closed.  rightType need not be closed.

Named `Conv.eitherInl_cong` (term-ctor perspective) so the
`#assert_conv_cong_coverage_budget` gate's exact-name matcher
recognises this as the `Term.eitherInl` cong mirror. -/
theorem Conv.eitherInl_cong
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
is closed.  leftType need not be closed.

Named `Conv.eitherInr_cong` (term-ctor perspective) so the
`#assert_conv_cong_coverage_budget` gate's exact-name matcher
recognises this as the `Term.eitherInr` cong mirror. -/
theorem Conv.eitherInr_cong
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

/-- True binary cong on both positions of `Term.listCons` when
element type is closed.  Composes the head and tail step lifts via
`Conv.cong2_at_isClosedTy` — no need for `Conv.trans` to combine
the two single-position rules above.

Named `Conv.listCons_cong` (term-ctor perspective) so the
`#assert_conv_cong_coverage_budget` gate's exact-name matcher
recognises this as the `Term.listCons` cong mirror. -/
theorem Conv.listCons_cong
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    {headRawA headRawB tailRawA tailRawB : RawTerm scope}
    {headTermA : Term context elementType headRawA}
    {headTermB : Term context elementType headRawB}
    {tailTermA : Term context (Ty.listType elementType) tailRawA}
    {tailTermB : Term context (Ty.listType elementType) tailRawB}
    (headConv : Conv headTermA headTermB)
    (tailConv : Conv tailTermA tailTermB) :
    Conv (Term.listCons headTermA tailTermA)
         (Term.listCons headTermB tailTermB) :=
  Conv.cong2_at_isClosedTy
    (resultTy := Ty.listType elementType)
    closedElement (IsClosedTy.listType closedElement)
    (wrapRaw := fun headRaw tailRaw =>
      RawTerm.listCons headRaw tailRaw)
    (fun headTerm tailTerm => Term.listCons headTerm tailTerm)
    (fun stepHead => Step.listConsHead stepHead)
    (fun stepTail => Step.listConsTail stepTail)
    headConv tailConv

/-! ## Record + codata closed-Ty cong rules

Single-field record introduction is unary; codata unfolding is
binary (state + transition).  Both consume the closed-Ty witness
catalog (`IsClosedTy.record` / `IsClosedTy.codata` / `IsClosedTy.arrow`)
to discharge SR through the wrapper positions. -/

/-- Conv cong on `Term.recordIntro`'s single field when the
underlying single-field type is closed.  Unary specialisation of
`cong_at_isClosedTy` at `IsClosedTy.record`.

Named `Conv.recordIntro_cong` (term-ctor perspective) so the
`#assert_conv_cong_coverage_budget` gate's exact-name matcher
recognises this as the `Term.recordIntro` cong mirror. -/
theorem Conv.recordIntro_cong
    {singleFieldType : Ty level scope}
    (closedSingleField : IsClosedTy singleFieldType)
    {fieldRawA fieldRawB : RawTerm scope}
    {fieldTermA : Term context singleFieldType fieldRawA}
    {fieldTermB : Term context singleFieldType fieldRawB}
    (fieldConv : Conv fieldTermA fieldTermB) :
    Conv (Term.recordIntro fieldTermA) (Term.recordIntro fieldTermB) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.record singleFieldType)
    closedSingleField
    (wrapRaw := RawTerm.recordIntro)
    (fun fieldTerm => Term.recordIntro fieldTerm)
    (fun step => Step.recordIntroField step)
    fieldConv

/-- Conv cong on both `Term.codataUnfold` positions (initial state
and transition function) when both component types are closed.
Binary specialisation of `cong2_at_isClosedTy` at `IsClosedTy.codata`.
The transition position carries `Ty.arrow stateType outputType`,
discharged via `IsClosedTy.arrow` from the closed components.

Named `Conv.codataUnfold_cong` (term-ctor perspective) so the
`#assert_conv_cong_coverage_budget` gate's exact-name matcher
recognises this as the `Term.codataUnfold` cong mirror. -/
theorem Conv.codataUnfold_cong
    {stateType outputType : Ty level scope}
    (closedState : IsClosedTy stateType)
    (closedOutput : IsClosedTy outputType)
    {stateRawA stateRawB transitionRawA transitionRawB : RawTerm scope}
    {stateTermA : Term context stateType stateRawA}
    {stateTermB : Term context stateType stateRawB}
    {transitionTermA :
      Term context (Ty.arrow stateType outputType) transitionRawA}
    {transitionTermB :
      Term context (Ty.arrow stateType outputType) transitionRawB}
    (stateConv : Conv stateTermA stateTermB)
    (transitionConv : Conv transitionTermA transitionTermB) :
    Conv (Term.codataUnfold stateTermA transitionTermA)
         (Term.codataUnfold stateTermB transitionTermB) :=
  Conv.cong2_at_isClosedTy
    (resultTy := Ty.codata stateType outputType)
    closedState (IsClosedTy.arrow closedState closedOutput)
    (wrapRaw := fun stateRaw transitionRaw =>
      RawTerm.codataUnfold stateRaw transitionRaw)
    (fun stateTerm transitionTerm =>
      Term.codataUnfold stateTerm transitionTerm)
    (fun stepState => Step.codataUnfoldState stepState)
    (fun stepTransition => Step.codataUnfoldTransition stepTransition)
    stateConv transitionConv

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

/-! ## Eliminator branch cong rules at closed motive types

For the no-payload branches (`nil`, `none`) at closed motive:
direct cong via Conv.cong_at_isClosedTy.

For the arrow-typed branches (`cons`, `some`, `left`, `right`):
combine `IsClosedTy.arrow` to express that the closed-component
+ closed-motive arrow is itself closed. -/

/-- Conv cong on `listElim`'s nil-branch position at closed motive. -/
theorem Conv.listElim_nil_cong_isClosedTy
    {elementType motiveType : Ty level scope}
    (closedMotive : IsClosedTy motiveType)
    {scrutRaw nilRawA nilRawB consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutRaw)
    {nilA : Term context motiveType nilRawA}
    {nilB : Term context motiveType nilRawB}
    (consBranch : Term context (Ty.arrow elementType
                                  (Ty.arrow (Ty.listType elementType) motiveType))
                                consRaw)
    (nilConv : Conv nilA nilB) :
    Conv (Term.listElim scrutinee nilA consBranch)
         (Term.listElim scrutinee nilB consBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType) closedMotive
    (wrapRaw := fun raw => RawTerm.listElim scrutRaw raw consRaw)
    (fun term => Term.listElim scrutinee term consBranch)
    (fun step => Step.listElimNil step)
    nilConv

/-- Conv cong on `listElim`'s cons-branch position at closed
elementType + closed motive (so the arrow type is closed). -/
theorem Conv.listElim_cons_cong_isClosedTy
    {elementType motiveType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (closedMotive : IsClosedTy motiveType)
    {scrutRaw nilRaw consRawA consRawB : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutRaw)
    (nilBranch : Term context motiveType nilRaw)
    {consA : Term context (Ty.arrow elementType
                            (Ty.arrow (Ty.listType elementType) motiveType))
                          consRawA}
    {consB : Term context (Ty.arrow elementType
                            (Ty.arrow (Ty.listType elementType) motiveType))
                          consRawB}
    (consConv : Conv consA consB) :
    Conv (Term.listElim scrutinee nilBranch consA)
         (Term.listElim scrutinee nilBranch consB) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.arrow closedElement
       (IsClosedTy.arrow (IsClosedTy.listType closedElement) closedMotive))
    (wrapRaw := fun raw => RawTerm.listElim scrutRaw nilRaw raw)
    (fun term => Term.listElim scrutinee nilBranch term)
    (fun step => Step.listElimCons step)
    consConv

/-- Conv cong on `optionMatch`'s none-branch position at closed motive. -/
theorem Conv.optionMatch_none_cong_isClosedTy
    {elementType motiveType : Ty level scope}
    (closedMotive : IsClosedTy motiveType)
    {scrutRaw noneRawA noneRawB someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutRaw)
    {noneA : Term context motiveType noneRawA}
    {noneB : Term context motiveType noneRawB}
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (noneConv : Conv noneA noneB) :
    Conv (Term.optionMatch scrutinee noneA someBranch)
         (Term.optionMatch scrutinee noneB someBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType) closedMotive
    (wrapRaw := fun raw => RawTerm.optionMatch scrutRaw raw someRaw)
    (fun term => Term.optionMatch scrutinee term someBranch)
    (fun step => Step.optionMatchNone step)
    noneConv

/-- Conv cong on `optionMatch`'s some-branch position at closed
elementType + closed motive. -/
theorem Conv.optionMatch_some_cong_isClosedTy
    {elementType motiveType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (closedMotive : IsClosedTy motiveType)
    {scrutRaw noneRaw someRawA someRawB : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutRaw)
    (noneBranch : Term context motiveType noneRaw)
    {someA : Term context (Ty.arrow elementType motiveType) someRawA}
    {someB : Term context (Ty.arrow elementType motiveType) someRawB}
    (someConv : Conv someA someB) :
    Conv (Term.optionMatch scrutinee noneBranch someA)
         (Term.optionMatch scrutinee noneBranch someB) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.arrow closedElement closedMotive)
    (wrapRaw := fun raw => RawTerm.optionMatch scrutRaw noneRaw raw)
    (fun term => Term.optionMatch scrutinee noneBranch term)
    (fun step => Step.optionMatchSome step)
    someConv

/-- Conv cong on `eitherMatch`'s left-branch position at closed
leftType + closed motive. -/
theorem Conv.eitherMatch_left_cong_isClosedTy
    {leftType rightType motiveType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    (closedMotive : IsClosedTy motiveType)
    {scrutRaw leftRawA leftRawB rightRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutRaw)
    {leftA : Term context (Ty.arrow leftType motiveType) leftRawA}
    {leftB : Term context (Ty.arrow leftType motiveType) leftRawB}
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (leftConv : Conv leftA leftB) :
    Conv (Term.eitherMatch scrutinee leftA rightBranch)
         (Term.eitherMatch scrutinee leftB rightBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.arrow closedLeft closedMotive)
    (wrapRaw := fun raw => RawTerm.eitherMatch scrutRaw raw rightRaw)
    (fun term => Term.eitherMatch scrutinee term rightBranch)
    (fun step => Step.eitherMatchLeft step)
    leftConv

/-- Conv cong on `eitherMatch`'s right-branch position at closed
rightType + closed motive. -/
theorem Conv.eitherMatch_right_cong_isClosedTy
    {leftType rightType motiveType : Ty level scope}
    (closedRight : IsClosedTy rightType)
    (closedMotive : IsClosedTy motiveType)
    {scrutRaw leftRaw rightRawA rightRawB : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    {rightA : Term context (Ty.arrow rightType motiveType) rightRawA}
    {rightB : Term context (Ty.arrow rightType motiveType) rightRawB}
    (rightConv : Conv rightA rightB) :
    Conv (Term.eitherMatch scrutinee leftBranch rightA)
         (Term.eitherMatch scrutinee leftBranch rightB) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.arrow closedRight closedMotive)
    (wrapRaw := fun raw => RawTerm.eitherMatch scrutRaw leftRaw raw)
    (fun term => Term.eitherMatch scrutinee leftBranch term)
    (fun step => Step.eitherMatchRight step)
    rightConv

/-! ## App-position cong rules at closed arrow types

For non-dependent application `app f a : codomain` where `f :
arrow domain codomain`: when both domain and codomain are
closed, the arrow type itself is closed (via `IsClosedTy.arrow`),
which lets us lift Conv on either the function or argument
position to Conv on the application.

These are load-bearing for Conv-transitivity across nested
redexes — without them, Conv on `f` cannot propagate through
`app f a` even when result type is closed. -/

/-- Conv cong on the function position of a non-dep app at
closed types.  Given Conv on `f` at `arrow domain codomain`
(both closed), produces Conv on `app f a` at `codomain`. -/
theorem Conv.appLeft_cong_isClosedTy
    {domainType codomainType : Ty level scope}
    (closedDomain : IsClosedTy domainType)
    (closedCodomain : IsClosedTy codomainType)
    {fnRawA fnRawB argRaw : RawTerm scope}
    {functionA : Term context (Ty.arrow domainType codomainType) fnRawA}
    {functionB : Term context (Ty.arrow domainType codomainType) fnRawB}
    (argumentTerm : Term context domainType argRaw)
    (functionConv : Conv functionA functionB) :
    Conv (Term.app functionA argumentTerm)
         (Term.app functionB argumentTerm) :=
  Conv.cong_at_isClosedTy
    (resultTy := codomainType)
    (IsClosedTy.arrow closedDomain closedCodomain)
    (wrapRaw := fun raw => RawTerm.app raw argRaw)
    (fun term => Term.app term argumentTerm)
    (fun step => Step.appLeft step)
    functionConv

/-- Conv cong on the argument position of a non-dep app at a
closed domain type.  Given Conv on `a` at `domain` (closed),
produces Conv on `app f a` at `codomain`. -/
theorem Conv.appRight_cong_isClosedTy
    {domainType codomainType : Ty level scope}
    (closedDomain : IsClosedTy domainType)
    {fnRaw argRawA argRawB : RawTerm scope}
    (functionTerm : Term context (Ty.arrow domainType codomainType) fnRaw)
    {argumentA : Term context domainType argRawA}
    {argumentB : Term context domainType argRawB}
    (argumentConv : Conv argumentA argumentB) :
    Conv (Term.app functionTerm argumentA)
         (Term.app functionTerm argumentB) :=
  Conv.cong_at_isClosedTy
    (resultTy := codomainType) closedDomain
    (wrapRaw := fun raw => RawTerm.app fnRaw raw)
    (fun term => Term.app functionTerm term)
    (fun step => Step.appRight step)
    argumentConv

/-- **Conv cong on `Term.app` at closed domain + codomain** —
both function and argument positions threaded simultaneously
via `cong2_at_isClosedTy`.  The arrow type
`Ty.arrow domainType codomainType` is closed via
`IsClosedTy.arrow`, satisfying the left-position closure premise.

Named `Conv.app_cong` (term-ctor perspective) so the
`#assert_conv_cong_coverage_budget` gate's exact-name matcher
recognises this as the `Term.app` cong mirror. -/
theorem Conv.app_cong
    {domainType codomainType : Ty level scope}
    (closedDomain : IsClosedTy domainType)
    (closedCodomain : IsClosedTy codomainType)
    {fnRawA fnRawB argRawA argRawB : RawTerm scope}
    {functionA : Term context (Ty.arrow domainType codomainType) fnRawA}
    {functionB : Term context (Ty.arrow domainType codomainType) fnRawB}
    {argumentA : Term context domainType argRawA}
    {argumentB : Term context domainType argRawB}
    (functionConv : Conv functionA functionB)
    (argumentConv : Conv argumentA argumentB) :
    Conv (Term.app functionA argumentA) (Term.app functionB argumentB) :=
  Conv.cong2_at_isClosedTy
    (resultTy := codomainType)
    (IsClosedTy.arrow closedDomain closedCodomain) closedDomain
    (wrapRaw := fun fnRaw argRaw => RawTerm.app fnRaw argRaw)
    (fun fnTerm argTerm => Term.app fnTerm argTerm)
    (fun stepFn => Step.appLeft stepFn)
    (fun stepArg => Step.appRight stepArg)
    functionConv argumentConv

/-! ## natElim/natRec succ-branch cong rules at closed motives

The succ-branches have arrow types: `arrow nat motive` for
natElim, `arrow nat (arrow motive motive)` for natRec.  When
the motive is closed, IsClosedTy.arrow gives the full arrow
closure. -/

/-- Conv cong on `natElim`'s succ-branch at a closed motive.
The succ-branch's type `arrow nat motive` is closed via
`IsClosedTy.arrow IsClosedTy.nat closedMotive`. -/
theorem Conv.natElimSucc_cong_isClosedTy
    {motiveType : Ty level scope}
    (closedMotive : IsClosedTy motiveType)
    {scrutRaw zeroRaw succRawA succRawB : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    {succBranchA : Term context (Ty.arrow Ty.nat motiveType) succRawA}
    {succBranchB : Term context (Ty.arrow Ty.nat motiveType) succRawB}
    (succConv : Conv succBranchA succBranchB) :
    Conv (Term.natElim scrutinee zeroBranch succBranchA)
         (Term.natElim scrutinee zeroBranch succBranchB) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.arrow IsClosedTy.nat closedMotive)
    (wrapRaw := fun raw => RawTerm.natElim scrutRaw zeroRaw raw)
    (fun term => Term.natElim scrutinee zeroBranch term)
    (fun step => Step.natElimSucc step)
    succConv

/-- Conv cong on `natRec`'s succ-branch at a closed motive.
The succ-branch's type `arrow nat (arrow motive motive)` is
closed via nested `IsClosedTy.arrow`. -/
theorem Conv.natRecSucc_cong_isClosedTy
    {motiveType : Ty level scope}
    (closedMotive : IsClosedTy motiveType)
    {scrutRaw zeroRaw succRawA succRawB : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    {succBranchA :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawA}
    {succBranchB :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawB}
    (succConv : Conv succBranchA succBranchB) :
    Conv (Term.natRec scrutinee zeroBranch succBranchA)
         (Term.natRec scrutinee zeroBranch succBranchB) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.arrow IsClosedTy.nat
       (IsClosedTy.arrow closedMotive closedMotive))
    (wrapRaw := fun raw => RawTerm.natRec scrutRaw zeroRaw raw)
    (fun term => Term.natRec scrutinee zeroBranch term)
    (fun step => Step.natRecSucc step)
    succConv

/-! ## Closed-Ty single-position cong rules for modal + projector ctors

The next batch of `_cong` rules covers Term ctors with a single
sub-Term position whose sub-position type is closed.  Each is a
~12-line specialization of `Conv.cong_at_isClosedTy`.

Coverage matrix (Term ctor ↔ Step ctor ↔ IsClosedTy ctor):

| Term ctor       | Step ctor           | IsClosedTy ctor  |
|-----------------|---------------------|------------------|
| modIntro        | Step.modIntroInner  | (innerType)      |
| modElim         | Step.modElimInner   | (innerType)      |
| subsume         | Step.subsumeInner   | (innerType)      |
| recordProj      | Step.recordProjRecord | record(closed) |
| codataDest      | Step.codataDestValue  | codata(closed,closed) |

`modIntro` / `modElim` / `subsume` preserve type (innerType in /
innerType out), so closedTy = resultTy = innerType.
`recordProj` and `codataDest` project the closed inner type to a
sub-component of the result. -/

/-- Conv cong on `Term.modIntro`'s inner position at a closed inner
type.  The modal carrier is closed, so `Term.modIntro` (which
preserves the underlying type) ships zero-axiom via the closed-type
lifter. -/
theorem Conv.modIntro_cong
    {innerType : Ty level scope}
    (closedInner : IsClosedTy innerType)
    {innerRawA innerRawB : RawTerm scope}
    {innerTermA : Term context innerType innerRawA}
    {innerTermB : Term context innerType innerRawB}
    (innerConv : Conv innerTermA innerTermB) :
    Conv (Term.modIntro innerTermA) (Term.modIntro innerTermB) :=
  Conv.cong_at_isClosedTy
    (resultTy := innerType)
    closedInner
    (wrapRaw := RawTerm.modIntro)
    (fun term => Term.modIntro term)
    (fun step => Step.modIntroInner step)
    innerConv

/-- Conv cong on `Term.modElim`'s inner position at a closed inner
type.  Same shape as `modIntro_cong` — `modElim` preserves the
underlying type. -/
theorem Conv.modElim_cong
    {innerType : Ty level scope}
    (closedInner : IsClosedTy innerType)
    {innerRawA innerRawB : RawTerm scope}
    {innerTermA : Term context innerType innerRawA}
    {innerTermB : Term context innerType innerRawB}
    (innerConv : Conv innerTermA innerTermB) :
    Conv (Term.modElim innerTermA) (Term.modElim innerTermB) :=
  Conv.cong_at_isClosedTy
    (resultTy := innerType)
    closedInner
    (wrapRaw := RawTerm.modElim)
    (fun term => Term.modElim term)
    (fun step => Step.modElimInner step)
    innerConv

/-- Conv cong on `Term.subsume`'s inner position at a closed inner
type.  Same shape as `modIntro_cong` — `subsume` preserves the
underlying type (mode/level cumulativity is in the carrier, not the
type). -/
theorem Conv.subsume_cong
    {innerType : Ty level scope}
    (closedInner : IsClosedTy innerType)
    {innerRawA innerRawB : RawTerm scope}
    {innerTermA : Term context innerType innerRawA}
    {innerTermB : Term context innerType innerRawB}
    (innerConv : Conv innerTermA innerTermB) :
    Conv (Term.subsume innerTermA) (Term.subsume innerTermB) :=
  Conv.cong_at_isClosedTy
    (resultTy := innerType)
    closedInner
    (wrapRaw := RawTerm.subsume)
    (fun term => Term.subsume term)
    (fun step => Step.subsumeInner step)
    innerConv

/-- Conv cong on `Term.recordProj`'s record position at a closed
single-field record type.  The result type is the closed
`singleFieldType` (one field per the current single-field record
spec). -/
theorem Conv.recordProj_cong
    {singleFieldType : Ty level scope}
    (closedSingleField : IsClosedTy singleFieldType)
    {recordRawA recordRawB : RawTerm scope}
    {recordValueA : Term context (Ty.record singleFieldType) recordRawA}
    {recordValueB : Term context (Ty.record singleFieldType) recordRawB}
    (recordConv : Conv recordValueA recordValueB) :
    Conv (Term.recordProj recordValueA) (Term.recordProj recordValueB) :=
  Conv.cong_at_isClosedTy
    (resultTy := singleFieldType)
    (IsClosedTy.record closedSingleField)
    (wrapRaw := RawTerm.recordProj)
    (fun term => Term.recordProj term)
    (fun step => Step.recordProjRecord step)
    recordConv

/-- Conv cong on `Term.refineIntro`'s two value positions
(baseValue at `baseType`, predicateProof at `Ty.unit`).  Only the
sub-position types need closure for the lifter to apply; the
result type `Ty.refine baseType predicate` itself is not in
`IsClosedTy` (refine carries a raw predicate binder, see
`Foundation/IsClosedTy.lean:131`), and that is fine — only the
sub-position constrains the SR intermediate.

`Ty.unit` is unconditionally closed via `IsClosedTy.unit`, so the
proof position closure is hard-wired. -/
theorem Conv.refineIntro_cong
    {baseType : Ty level scope}
    (closedBase : IsClosedTy baseType)
    {predicate : RawTerm (scope + 1)}
    {valueRawA valueRawB proofRawA proofRawB : RawTerm scope}
    {baseValueA : Term context baseType valueRawA}
    {baseValueB : Term context baseType valueRawB}
    {predicateProofA : Term context Ty.unit proofRawA}
    {predicateProofB : Term context Ty.unit proofRawB}
    (valueConv : Conv baseValueA baseValueB)
    (proofConv : Conv predicateProofA predicateProofB) :
    Conv (Term.refineIntro predicate baseValueA predicateProofA)
         (Term.refineIntro predicate baseValueB predicateProofB) :=
  Conv.cong2_at_isClosedTy
    (resultTy := Ty.refine baseType predicate)
    closedBase
    IsClosedTy.unit
    (wrapRaw := fun valueRaw proofRaw =>
      RawTerm.refineIntro valueRaw proofRaw)
    (fun baseValue predicateProof =>
      Term.refineIntro predicate baseValue predicateProof)
    (fun stepValue => Step.refineIntroValue stepValue)
    (fun stepProof => Step.refineIntroProof stepProof)
    valueConv proofConv

/-- Conv cong on `Term.codataDest`'s codata position at a closed
codata type.  The result type is the closed `outputType` component
of the codata. -/
theorem Conv.codataDest_cong
    {stateType outputType : Ty level scope}
    (closedState : IsClosedTy stateType)
    (closedOutput : IsClosedTy outputType)
    {codataRawA codataRawB : RawTerm scope}
    {codataValueA : Term context (Ty.codata stateType outputType) codataRawA}
    {codataValueB : Term context (Ty.codata stateType outputType) codataRawB}
    (codataConv : Conv codataValueA codataValueB) :
    Conv (Term.codataDest codataValueA) (Term.codataDest codataValueB) :=
  Conv.cong_at_isClosedTy
    (resultTy := outputType)
    (IsClosedTy.codata closedState closedOutput)
    (wrapRaw := RawTerm.codataDest)
    (fun term => Term.codataDest term)
    (fun step => Step.codataDestValue step)
    codataConv

/-! ## Ternary lifter — three closed sub-positions

`Conv.cong3_at_isClosedTy` generalises `cong2_at_isClosedTy` to a
three-position wrapper.  Each sub-position carries its own closed
type, its own SR-applicable existential extraction, and its own
per-position Step cong rule.  Internally three applications of
`StepStar.lift_at_isClosedTy` are composed via two
`StepStar.append`s: vary first position keeping the other two at
source raws, then second keeping first at its mid reduct and third
at source raw, then third keeping first and second at mid reducts.

The lifter unlocks per-ctor `_cong` budget-gate matchers for
3-position recursor ctors (listElim, optionMatch, eitherMatch,
natElim, natRec) whose motive type is closed — these no longer
need three separate `_<position>_cong_isClosedTy` rules at call
sites.  The existing per-position rules remain in the kernel as
single-arrow specialisations of `cong_at_isClosedTy`. -/

/-- Generic 3-arg Conv-level cong rule at three closed sub-positions.
Composes via two `StepStar.append`s + per-position
`StepStar.lift_at_isClosedTy`. -/
theorem Conv.cong3_at_isClosedTy
    {firstClosedTy secondClosedTy thirdClosedTy resultTy : Ty level scope}
    (firstIsClosed : IsClosedTy firstClosedTy)
    (secondIsClosed : IsClosedTy secondClosedTy)
    (thirdIsClosed : IsClosedTy thirdClosedTy)
    {wrapRaw : RawTerm scope → RawTerm scope → RawTerm scope → RawTerm scope}
    (wrap : ∀ {firstRaw secondRaw thirdRaw : RawTerm scope},
            Term context firstClosedTy firstRaw →
            Term context secondClosedTy secondRaw →
            Term context thirdClosedTy thirdRaw →
            Term context resultTy (wrapRaw firstRaw secondRaw thirdRaw))
    (stepWrapFirst :
      ∀ {firstSourceRaw firstTargetRaw secondRaw thirdRaw : RawTerm scope}
        {firstSourceTerm : Term context firstClosedTy firstSourceRaw}
        {firstTargetTerm : Term context firstClosedTy firstTargetRaw}
        {secondTerm : Term context secondClosedTy secondRaw}
        {thirdTerm : Term context thirdClosedTy thirdRaw},
        Step firstSourceTerm firstTargetTerm →
        Step (wrap firstSourceTerm secondTerm thirdTerm)
             (wrap firstTargetTerm secondTerm thirdTerm))
    (stepWrapSecond :
      ∀ {firstRaw secondSourceRaw secondTargetRaw thirdRaw : RawTerm scope}
        {firstTerm : Term context firstClosedTy firstRaw}
        {secondSourceTerm : Term context secondClosedTy secondSourceRaw}
        {secondTargetTerm : Term context secondClosedTy secondTargetRaw}
        {thirdTerm : Term context thirdClosedTy thirdRaw},
        Step secondSourceTerm secondTargetTerm →
        Step (wrap firstTerm secondSourceTerm thirdTerm)
             (wrap firstTerm secondTargetTerm thirdTerm))
    (stepWrapThird :
      ∀ {firstRaw secondRaw thirdSourceRaw thirdTargetRaw : RawTerm scope}
        {firstTerm : Term context firstClosedTy firstRaw}
        {secondTerm : Term context secondClosedTy secondRaw}
        {thirdSourceTerm : Term context thirdClosedTy thirdSourceRaw}
        {thirdTargetTerm : Term context thirdClosedTy thirdTargetRaw},
        Step thirdSourceTerm thirdTargetTerm →
        Step (wrap firstTerm secondTerm thirdSourceTerm)
             (wrap firstTerm secondTerm thirdTargetTerm))
    {firstSrcRaw firstTgtRaw secondSrcRaw secondTgtRaw
     thirdSrcRaw thirdTgtRaw : RawTerm scope}
    {firstSrcTerm : Term context firstClosedTy firstSrcRaw}
    {firstTgtTerm : Term context firstClosedTy firstTgtRaw}
    {secondSrcTerm : Term context secondClosedTy secondSrcRaw}
    {secondTgtTerm : Term context secondClosedTy secondTgtRaw}
    {thirdSrcTerm : Term context thirdClosedTy thirdSrcRaw}
    {thirdTgtTerm : Term context thirdClosedTy thirdTgtRaw}
    (firstConv : Conv firstSrcTerm firstTgtTerm)
    (secondConv : Conv secondSrcTerm secondTgtTerm)
    (thirdConv : Conv thirdSrcTerm thirdTgtTerm) :
    Conv (wrap firstSrcTerm secondSrcTerm thirdSrcTerm)
         (wrap firstTgtTerm secondTgtTerm thirdTgtTerm) := by
  obtain ⟨midFirstType, midFirstRaw, midFirstTerm,
          firstChainA, firstChainB⟩ := firstConv
  obtain ⟨midSecondType, midSecondRaw, midSecondTerm,
          secondChainA, secondChainB⟩ := secondConv
  obtain ⟨midThirdType, midThirdRaw, midThirdTerm,
          thirdChainA, thirdChainB⟩ := thirdConv
  have midFirstIsClosed : midFirstType = firstClosedTy :=
    StepStar.preserves_isClosedTy firstIsClosed firstChainA rfl
  have midSecondIsClosed : midSecondType = secondClosedTy :=
    StepStar.preserves_isClosedTy secondIsClosed secondChainA rfl
  have midThirdIsClosed : midThirdType = thirdClosedTy :=
    StepStar.preserves_isClosedTy thirdIsClosed thirdChainA rfl
  cases midFirstIsClosed
  cases midSecondIsClosed
  cases midThirdIsClosed
  refine ⟨resultTy, _, wrap midFirstTerm midSecondTerm midThirdTerm, ?_, ?_⟩
  · have firstVariation :
        StepStar (wrap firstSrcTerm secondSrcTerm thirdSrcTerm)
                 (wrap midFirstTerm secondSrcTerm thirdSrcTerm) :=
      StepStar.lift_at_isClosedTy firstIsClosed
        (fun firstTerm => wrap firstTerm secondSrcTerm thirdSrcTerm)
        (fun stepFirst => stepWrapFirst stepFirst)
        firstChainA rfl rfl
    have secondVariation :
        StepStar (wrap midFirstTerm secondSrcTerm thirdSrcTerm)
                 (wrap midFirstTerm midSecondTerm thirdSrcTerm) :=
      StepStar.lift_at_isClosedTy secondIsClosed
        (fun secondTerm => wrap midFirstTerm secondTerm thirdSrcTerm)
        (fun stepSecond => stepWrapSecond stepSecond)
        secondChainA rfl rfl
    have thirdVariation :
        StepStar (wrap midFirstTerm midSecondTerm thirdSrcTerm)
                 (wrap midFirstTerm midSecondTerm midThirdTerm) :=
      StepStar.lift_at_isClosedTy thirdIsClosed
        (fun thirdTerm => wrap midFirstTerm midSecondTerm thirdTerm)
        (fun stepThird => stepWrapThird stepThird)
        thirdChainA rfl rfl
    exact StepStar.append (StepStar.append firstVariation secondVariation)
                          thirdVariation
  · have firstVariation :
        StepStar (wrap firstTgtTerm secondTgtTerm thirdTgtTerm)
                 (wrap midFirstTerm secondTgtTerm thirdTgtTerm) :=
      StepStar.lift_at_isClosedTy firstIsClosed
        (fun firstTerm => wrap firstTerm secondTgtTerm thirdTgtTerm)
        (fun stepFirst => stepWrapFirst stepFirst)
        firstChainB rfl rfl
    have secondVariation :
        StepStar (wrap midFirstTerm secondTgtTerm thirdTgtTerm)
                 (wrap midFirstTerm midSecondTerm thirdTgtTerm) :=
      StepStar.lift_at_isClosedTy secondIsClosed
        (fun secondTerm => wrap midFirstTerm secondTerm thirdTgtTerm)
        (fun stepSecond => stepWrapSecond stepSecond)
        secondChainB rfl rfl
    have thirdVariation :
        StepStar (wrap midFirstTerm midSecondTerm thirdTgtTerm)
                 (wrap midFirstTerm midSecondTerm midThirdTerm) :=
      StepStar.lift_at_isClosedTy thirdIsClosed
        (fun thirdTerm => wrap midFirstTerm midSecondTerm thirdTerm)
        (fun stepThird => stepWrapThird stepThird)
        thirdChainB rfl rfl
    exact StepStar.append (StepStar.append firstVariation secondVariation)
                          thirdVariation

/-! ## Recursor cong rules via cong3

Each `Conv.<recursor>_cong` varies all three positions
simultaneously, with closure premises on the relevant carrier
types.  All five recursors share the non-dep motive shape
(`motiveType : Ty level scope`); the dependent-motive refactor in
K07.1-K07.5 will require a different lifter once shipped. -/

/-- Conv cong on `Term.listElim` varying all three positions
(scrutinee, nilBranch, consBranch) at closed element + motive
types. -/
theorem Conv.listElim_cong
    {elementType motiveType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (closedMotive : IsClosedTy motiveType)
    {scrutRawA scrutRawB nilRawA nilRawB consRawA consRawB : RawTerm scope}
    {scrutA : Term context (Ty.listType elementType) scrutRawA}
    {scrutB : Term context (Ty.listType elementType) scrutRawB}
    {nilA : Term context motiveType nilRawA}
    {nilB : Term context motiveType nilRawB}
    {consA : Term context (Ty.arrow elementType
                            (Ty.arrow (Ty.listType elementType) motiveType))
                          consRawA}
    {consB : Term context (Ty.arrow elementType
                            (Ty.arrow (Ty.listType elementType) motiveType))
                          consRawB}
    (scrutConv : Conv scrutA scrutB)
    (nilConv : Conv nilA nilB)
    (consConv : Conv consA consB) :
    Conv (Term.listElim scrutA nilA consA)
         (Term.listElim scrutB nilB consB) :=
  Conv.cong3_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.listType closedElement)
    closedMotive
    (IsClosedTy.arrow closedElement
       (IsClosedTy.arrow (IsClosedTy.listType closedElement) closedMotive))
    (wrapRaw := fun scrutRaw nilRaw consRaw =>
      RawTerm.listElim scrutRaw nilRaw consRaw)
    (fun scrutTerm nilTerm consTerm => Term.listElim scrutTerm nilTerm consTerm)
    (fun stepScrut => Step.listElimScrutinee stepScrut)
    (fun stepNil => Step.listElimNil stepNil)
    (fun stepCons => Step.listElimCons stepCons)
    scrutConv nilConv consConv

/-- Conv cong on `Term.optionMatch` varying all three positions
(scrutinee, noneBranch, someBranch) at closed element + motive
types. -/
theorem Conv.optionMatch_cong
    {elementType motiveType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (closedMotive : IsClosedTy motiveType)
    {scrutRawA scrutRawB noneRawA noneRawB someRawA someRawB : RawTerm scope}
    {scrutA : Term context (Ty.optionType elementType) scrutRawA}
    {scrutB : Term context (Ty.optionType elementType) scrutRawB}
    {noneA : Term context motiveType noneRawA}
    {noneB : Term context motiveType noneRawB}
    {someA : Term context (Ty.arrow elementType motiveType) someRawA}
    {someB : Term context (Ty.arrow elementType motiveType) someRawB}
    (scrutConv : Conv scrutA scrutB)
    (noneConv : Conv noneA noneB)
    (someConv : Conv someA someB) :
    Conv (Term.optionMatch scrutA noneA someA)
         (Term.optionMatch scrutB noneB someB) :=
  Conv.cong3_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.optionType closedElement)
    closedMotive
    (IsClosedTy.arrow closedElement closedMotive)
    (wrapRaw := fun scrutRaw noneRaw someRaw =>
      RawTerm.optionMatch scrutRaw noneRaw someRaw)
    (fun scrutTerm noneTerm someTerm =>
      Term.optionMatch scrutTerm noneTerm someTerm)
    (fun stepScrut => Step.optionMatchScrutinee stepScrut)
    (fun stepNone => Step.optionMatchNone stepNone)
    (fun stepSome => Step.optionMatchSome stepSome)
    scrutConv noneConv someConv

/-- Conv cong on `Term.eitherMatch` varying all three positions
(scrutinee, leftBranch, rightBranch) at closed left/right/motive
types. -/
theorem Conv.eitherMatch_cong
    {leftType rightType motiveType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    (closedRight : IsClosedTy rightType)
    (closedMotive : IsClosedTy motiveType)
    {scrutRawA scrutRawB leftRawA leftRawB rightRawA rightRawB : RawTerm scope}
    {scrutA : Term context (Ty.eitherType leftType rightType) scrutRawA}
    {scrutB : Term context (Ty.eitherType leftType rightType) scrutRawB}
    {leftA : Term context (Ty.arrow leftType motiveType) leftRawA}
    {leftB : Term context (Ty.arrow leftType motiveType) leftRawB}
    {rightA : Term context (Ty.arrow rightType motiveType) rightRawA}
    {rightB : Term context (Ty.arrow rightType motiveType) rightRawB}
    (scrutConv : Conv scrutA scrutB)
    (leftConv : Conv leftA leftB)
    (rightConv : Conv rightA rightB) :
    Conv (Term.eitherMatch scrutA leftA rightA)
         (Term.eitherMatch scrutB leftB rightB) :=
  Conv.cong3_at_isClosedTy
    (resultTy := motiveType)
    (IsClosedTy.eitherType closedLeft closedRight)
    (IsClosedTy.arrow closedLeft closedMotive)
    (IsClosedTy.arrow closedRight closedMotive)
    (wrapRaw := fun scrutRaw leftRaw rightRaw =>
      RawTerm.eitherMatch scrutRaw leftRaw rightRaw)
    (fun scrutTerm leftTerm rightTerm =>
      Term.eitherMatch scrutTerm leftTerm rightTerm)
    (fun stepScrut => Step.eitherMatchScrutinee stepScrut)
    (fun stepLeft => Step.eitherMatchLeft stepLeft)
    (fun stepRight => Step.eitherMatchRight stepRight)
    scrutConv leftConv rightConv

/-- Conv cong on `Term.natElim` varying all three positions
(scrutinee, zeroBranch, succBranch) at closed motive.  Scrutinee
sits at `Ty.nat` (unconditionally closed via `IsClosedTy.nat`). -/
theorem Conv.natElim_cong
    {motiveType : Ty level scope}
    (closedMotive : IsClosedTy motiveType)
    {scrutRawA scrutRawB zeroRawA zeroRawB succRawA succRawB : RawTerm scope}
    {scrutA : Term context Ty.nat scrutRawA}
    {scrutB : Term context Ty.nat scrutRawB}
    {zeroA : Term context motiveType zeroRawA}
    {zeroB : Term context motiveType zeroRawB}
    {succA : Term context (Ty.arrow Ty.nat motiveType) succRawA}
    {succB : Term context (Ty.arrow Ty.nat motiveType) succRawB}
    (scrutConv : Conv scrutA scrutB)
    (zeroConv : Conv zeroA zeroB)
    (succConv : Conv succA succB) :
    Conv (Term.natElim scrutA zeroA succA)
         (Term.natElim scrutB zeroB succB) :=
  Conv.cong3_at_isClosedTy
    (resultTy := motiveType)
    IsClosedTy.nat
    closedMotive
    (IsClosedTy.arrow IsClosedTy.nat closedMotive)
    (wrapRaw := fun scrutRaw zeroRaw succRaw =>
      RawTerm.natElim scrutRaw zeroRaw succRaw)
    (fun scrutTerm zeroTerm succTerm =>
      Term.natElim scrutTerm zeroTerm succTerm)
    (fun stepScrut => Step.natElimScrutinee stepScrut)
    (fun stepZero => Step.natElimZero stepZero)
    (fun stepSucc => Step.natElimSucc stepSucc)
    scrutConv zeroConv succConv

/-- Conv cong on `Term.natRec` varying all three positions
(scrutinee, zeroBranch, succBranch) at closed motive.  succBranch's
type is `arrow nat (arrow motive motive)`. -/
theorem Conv.natRec_cong
    {motiveType : Ty level scope}
    (closedMotive : IsClosedTy motiveType)
    {scrutRawA scrutRawB zeroRawA zeroRawB succRawA succRawB : RawTerm scope}
    {scrutA : Term context Ty.nat scrutRawA}
    {scrutB : Term context Ty.nat scrutRawB}
    {zeroA : Term context motiveType zeroRawA}
    {zeroB : Term context motiveType zeroRawB}
    {succA :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawA}
    {succB :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawB}
    (scrutConv : Conv scrutA scrutB)
    (zeroConv : Conv zeroA zeroB)
    (succConv : Conv succA succB) :
    Conv (Term.natRec scrutA zeroA succA)
         (Term.natRec scrutB zeroB succB) :=
  Conv.cong3_at_isClosedTy
    (resultTy := motiveType)
    IsClosedTy.nat
    closedMotive
    (IsClosedTy.arrow IsClosedTy.nat
       (IsClosedTy.arrow closedMotive closedMotive))
    (wrapRaw := fun scrutRaw zeroRaw succRaw =>
      RawTerm.natRec scrutRaw zeroRaw succRaw)
    (fun scrutTerm zeroTerm succTerm =>
      Term.natRec scrutTerm zeroTerm succTerm)
    (fun stepScrut => Step.natRecScrutinee stepScrut)
    (fun stepZero => Step.natRecZero stepZero)
    (fun stepSucc => Step.natRecSucc stepSucc)
    scrutConv zeroConv succConv

end LeanFX2
