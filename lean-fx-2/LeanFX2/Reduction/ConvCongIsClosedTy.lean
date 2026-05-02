import LeanFX2.Term.SubjectReductionGeneral
import LeanFX2.Reduction.Conv

/-! # Reduction/ConvCongIsClosedTy — generic cong-rule lifter at closed types

When a cong rule applies a Step inside a sub-position whose type is
closed (`IsClosedTy`), the closed-type SR theorem
(`Step.preserves_isClosedTy`) constrains every intermediate type in
a `StepStar` chain to be the same closed type.  This makes lifting a
chain on the sub-position to a chain on the wrapped term a uniform
8-line proof — independent of which Step cong rule is involved.

This file ships:

* `StepStar.lift_at_isClosedTy` — generic lifter parameterized by
  the wrapper (a Term → Term function) and a Step cong rule that
  lifts Step on the sub-position to Step on the wrapped term.

* `Conv.cong_at_isClosedTy` — Conv-level lifter via existential
  extraction + SR + re-wrap.

These subsume the per-ctor cong rules
(`StepStar.natSucc_lift`, `StepStar.idJ_baseCase_lift_isClosedTy`,
etc.).  The per-ctor rules become 1-line corollaries
parameterizing this helper at the matching wrapper + Step ctor.

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

/-- Generic StepStar lifter at a closed sub-position.

Given:
* `closedTyIsClosed : IsClosedTy closedTy` — closed sub-position type
* `wrap` — the Term-level wrapper (e.g., `fun t => Term.natSucc t`)
* `stepWrap` — the Step cong rule (e.g., `Step.natSuccPred`)
* a chain on the sub-position (typed at `closedTy` via
  `srcIsClosed`/`tgtIsClosed`)

Produces a chain on the wrapped terms.  Discharged by induction
on the chain; the `step` case bridges the intermediate type back
to `closedTy` via `Step.preserves_isClosedTy`. -/
theorem StepStar.lift_at_isClosedTy
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
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsClosed : srcTy = closedTy)
    (tgtIsClosed : tgtTy = closedTy) :
    StepStar (wrap (srcIsClosed ▸ srcTerm))
             (wrap (tgtIsClosed ▸ tgtTerm)) := by
  induction someChain with
  | refl _ =>
      cases srcIsClosed
      cases tgtIsClosed
      exact StepStar.refl _
  | step head _ tailIH =>
      have midIsClosed : _ = closedTy :=
        Step.preserves_isClosedTy closedTyIsClosed head srcIsClosed
      cases srcIsClosed
      cases midIsClosed
      exact StepStar.step (stepWrap head) (tailIH rfl tgtIsClosed)

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

end LeanFX2
