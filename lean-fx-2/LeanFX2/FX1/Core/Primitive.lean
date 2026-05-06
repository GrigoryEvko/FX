prelude
import Init.Prelude

/-! # FX1/Core/Primitive

Root status: Root-FX1 primitive aperture.

This is the only FX1/Core module that imports `Init.Prelude` directly. It
defines the tiny executable primitives whose behavior the root checker needs
without delegating equality to host `String`, host `Nat.beq`, or Lean's
decidable-equality machinery.
-/

namespace LeanFX2.FX1

/-- Result of structural equality comparison with a proof payload in the equal
case. -/
inductive EqualityResult {valueType : Type} (leftValue rightValue : valueType) :
    Type
  /-- The compared values are equal. -/
  | equal (valuesEqual : Eq leftValue rightValue) :
      EqualityResult leftValue rightValue
  /-- The compared values are structurally different. -/
  | notEqual : EqualityResult leftValue rightValue

namespace Boolean

/-- If a Boolean conjunction is true, its left side is true. -/
theorem and_true_left {leftBool rightBool : Bool}
    (andIsTrue : Eq (Bool.and leftBool rightBool) true) :
    Eq leftBool true :=
  match leftBool, rightBool with
  | true, true => Eq.refl true
  | true, false => Eq.refl true
  | false, true => nomatch andIsTrue
  | false, false => nomatch andIsTrue

/-- If a Boolean conjunction is true, its right side is true. -/
theorem and_true_right {leftBool rightBool : Bool}
    (andIsTrue : Eq (Bool.and leftBool rightBool) true) :
    Eq rightBool true :=
  match leftBool, rightBool with
  | true, true => Eq.refl true
  | true, false => nomatch andIsTrue
  | false, true => Eq.refl true
  | false, false => nomatch andIsTrue

end Boolean

namespace NaturalNumber

/-- FX1-native structural equality for natural numbers.

This intentionally avoids host `Nat.beq`, whose implementation is an external
runtime primitive in Lean's host environment. -/
def beq : Nat -> Nat -> Bool
  | Nat.zero, Nat.zero => true
  | Nat.zero, Nat.succ _ => false
  | Nat.succ _, Nat.zero => false
  | Nat.succ leftSmallerIndex, Nat.succ rightSmallerIndex =>
      NaturalNumber.beq leftSmallerIndex rightSmallerIndex

/-- Soundness of FX1-native natural-number equality. -/
theorem beq_sound
    : forall leftIndex rightIndex : Nat,
      Eq (NaturalNumber.beq leftIndex rightIndex) true ->
      Eq leftIndex rightIndex
  | Nat.zero, Nat.zero, _ => Eq.refl Nat.zero
  | Nat.zero, Nat.succ _, equalityIsTrue => nomatch equalityIsTrue
  | Nat.succ _, Nat.zero, equalityIsTrue => nomatch equalityIsTrue
  | Nat.succ leftSmallerIndex, Nat.succ rightSmallerIndex, equalityIsTrue =>
      congrArg Nat.succ
        (NaturalNumber.beq_sound
          leftSmallerIndex
          rightSmallerIndex
          equalityIsTrue)

/-- Proof-carrying natural-number comparison for executable checkers that need
an equality witness without passing through Boolean contradiction lemmas. -/
def eqResult : (leftIndex rightIndex : Nat) ->
    EqualityResult leftIndex rightIndex
  | Nat.zero, Nat.zero => EqualityResult.equal (Eq.refl Nat.zero)
  | Nat.zero, Nat.succ _ => EqualityResult.notEqual
  | Nat.succ _, Nat.zero => EqualityResult.notEqual
  | Nat.succ leftSmallerIndex, Nat.succ rightSmallerIndex =>
      match NaturalNumber.eqResult leftSmallerIndex rightSmallerIndex with
      | EqualityResult.equal smallerEquality =>
          EqualityResult.equal (congrArg Nat.succ smallerEquality)
      | EqualityResult.notEqual => EqualityResult.notEqual

end NaturalNumber

end LeanFX2.FX1
