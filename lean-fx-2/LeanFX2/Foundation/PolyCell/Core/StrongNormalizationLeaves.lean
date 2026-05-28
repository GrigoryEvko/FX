import LeanFX2.Foundation.PolyCell.Core.StepStarConfluence

/-! # Foundation/PolyCell/Core/StrongNormalizationLeaves
    - first concrete v2 SN endpoints

This starts the M9/M10 strong-normalization lane with real accessibility
witnesses, not a placeholder reducibility predicate.  The theorems here prove
that closed nullary normal leaves have no outgoing `Step`, and therefore are
`IsStronglyNormalizing` for the `StepSuccessor` relation consumed by the M8
Newman bridge.
-/

namespace LeanFX2.Foundation.PolyCell.Core
namespace StepStar

/-- If a term has no outgoing one-step reducts, it is accessible under the
one-step-successor relation. -/
theorem isStronglyNormalizing_of_noStep {scope : Nat}
    {sourceTerm : RawTerm scope}
    (hasNoStep : ∀ targetTerm : RawTerm scope, Step sourceTerm targetTerm → False) :
    IsStronglyNormalizing sourceTerm :=
  Acc.intro sourceTerm
    (fun targetTerm successorStep =>
      False.elim (hasNoStep targetTerm successorStep))

/-- The empty child spine cannot take a child step. -/
theorem noStepChildren_childNil {scope : Nat}
    {targetChildren : RawTermChildren [] scope} :
    StepChildren (.childNil : RawTermChildren [] scope) targetChildren →
      False := by
  intro childStep
  cases childStep

/-- `unit` is a normal leaf: it has no outgoing v2 `Step`. -/
theorem noStep_unit {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_unit () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- `boolTrue` is a normal leaf. -/
theorem noStep_boolTrue {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_boolTrue () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- `boolFalse` is a normal leaf. -/
theorem noStep_boolFalse {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_boolFalse () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- `natZero` is a normal leaf. -/
theorem noStep_natZero {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_natZero () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- `listNil` is a normal leaf. -/
theorem noStep_listNil {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_listNil () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- `optionNone` is a normal leaf. -/
theorem noStep_optionNone {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_optionNone () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- The certified unit fixture is strongly normalizing. -/
theorem unit_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_unit () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_unit (targetTerm := targetTerm) step)

/-- The certified `boolTrue` fixture is strongly normalizing. -/
theorem boolTrue_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_boolTrue () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_boolTrue (targetTerm := targetTerm) step)

/-- The certified `boolFalse` fixture is strongly normalizing. -/
theorem boolFalse_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_boolFalse () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_boolFalse (targetTerm := targetTerm) step)

/-- The certified `natZero` fixture is strongly normalizing. -/
theorem natZero_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_natZero () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_natZero (targetTerm := targetTerm) step)

/-- The certified `listNil` fixture is strongly normalizing. -/
theorem listNil_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_listNil () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_listNil (targetTerm := targetTerm) step)

/-- The certified `optionNone` fixture is strongly normalizing. -/
theorem optionNone_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_optionNone () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_optionNone (targetTerm := targetTerm) step)

end StepStar
end LeanFX2.Foundation.PolyCell.Core
