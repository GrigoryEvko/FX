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

/-- Variables are normal leaves: they have no outgoing v2 `Step`. -/
theorem noStep_var {scope : Nat} (index : Fin scope)
    {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_var index .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

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

/-- A universe-code atom is a normal leaf. -/
theorem noStep_universeCode {scope : Nat} (levelCode : Nat)
    {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_universeCode levelCode .childNil : RawTerm scope)
        targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- Cubical interval endpoint `0` is a normal leaf. -/
theorem noStep_interval0 {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_interval0 () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- Cubical interval endpoint `1` is a normal leaf. -/
theorem noStep_interval1 {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_interval1 () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- The HIT circle base point is a normal leaf in the current raw
reduction system. -/
theorem noStep_circleBase {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_circleBase () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- The HIT circle loop generator is a normal leaf in the current raw
reduction system. -/
theorem noStep_circleLoop {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_circleLoop () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- A quantum-bit atom is a normal leaf in the current raw reduction system. -/
theorem noStep_qubit {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_qubit () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- A hyperreal atom is a normal leaf in the current raw reduction system. -/
theorem noStep_hyperreal {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_hyperreal () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- Variables are strongly normalizing. -/
theorem var_isStronglyNormalizing {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing
      (.mkGen .gen_var index .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step =>
      noStep_var index (targetTerm := targetTerm) step)

/-- The unit leaf is strongly normalizing. -/
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

/-- Universe-code atoms are strongly normalizing. -/
theorem universeCode_isStronglyNormalizing {scope : Nat} (levelCode : Nat) :
    IsStronglyNormalizing
      (.mkGen .gen_universeCode levelCode .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step =>
      noStep_universeCode levelCode (targetTerm := targetTerm) step)

/-- Cubical interval endpoint `0` is strongly normalizing. -/
theorem interval0_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_interval0 () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_interval0 (targetTerm := targetTerm) step)

/-- Cubical interval endpoint `1` is strongly normalizing. -/
theorem interval1_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_interval1 () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_interval1 (targetTerm := targetTerm) step)

/-- The HIT circle base point is strongly normalizing in the current raw
reduction system. -/
theorem circleBase_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_circleBase () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_circleBase (targetTerm := targetTerm) step)

/-- The HIT circle loop generator is strongly normalizing in the current raw
reduction system. -/
theorem circleLoop_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_circleLoop () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_circleLoop (targetTerm := targetTerm) step)

/-- Quantum-bit atoms are strongly normalizing in the current raw reduction
system. -/
theorem qubit_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_qubit () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_qubit (targetTerm := targetTerm) step)

/-- Hyperreal atoms are strongly normalizing in the current raw reduction
system. -/
theorem hyperreal_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_hyperreal () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_hyperreal (targetTerm := targetTerm) step)

end StepStar
end LeanFX2.Foundation.PolyCell.Core
