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

namespace Boolean

/-- Proof-carrying structural comparison for booleans.

Avoids host `Bool.beq` and Lean's auto-derived `DecidableEq Bool` (the
auto-derivation pulls in `propext` through the equation compiler when
the result type is later eliminated dependently).  Four enumerated
arms; equal cases return `Eq.refl`. -/
def eqResult : (leftBool rightBool : Bool) ->
    EqualityResult leftBool rightBool
  | true, true => EqualityResult.equal (Eq.refl true)
  | true, false => EqualityResult.notEqual
  | false, true => EqualityResult.notEqual
  | false, false => EqualityResult.equal (Eq.refl false)

end Boolean

namespace ListPayload

/-- Proof-carrying structural comparison for lists, parametrised by a
per-element comparator.

The element comparator must produce an `EqualityResult` carrying an
`Eq` witness on the equal case; the four list arms (nil/nil,
nil/cons, cons/nil, cons/cons) lift those witnesses through
`congrArg` + `Eq.trans` over the cons constructor.

Used by `MData.eqResult` (List of MDataEntry) and by `Expr.eqResult`
in the `Expr.const _ levels` arm (List of Level).  Keeping the
recursion on `leftList` makes structural-recursion termination
obvious. -/
def eqResult {alpha : Type}
    (elementEq :
      (leftElement rightElement : alpha) ->
        EqualityResult leftElement rightElement) :
    (leftList rightList : List alpha) -> EqualityResult leftList rightList
  | List.nil, List.nil =>
      EqualityResult.equal (Eq.refl (List.nil : List alpha))
  | List.nil, List.cons _rightHead _rightTail => EqualityResult.notEqual
  | List.cons _leftHead _leftTail, List.nil => EqualityResult.notEqual
  | List.cons leftHead leftTail, List.cons rightHead rightTail =>
      match elementEq leftHead rightHead with
      | EqualityResult.equal headEquality =>
          match eqResult elementEq leftTail rightTail with
          | EqualityResult.equal tailEquality =>
              EqualityResult.equal
                (Eq.trans
                  (congrArg
                    (fun rewrittenHead =>
                      List.cons rewrittenHead leftTail)
                    headEquality)
                  (congrArg
                    (fun rewrittenTail =>
                      List.cons rightHead rewrittenTail)
                    tailEquality))
          | EqualityResult.notEqual => EqualityResult.notEqual
      | EqualityResult.notEqual => EqualityResult.notEqual

end ListPayload

end LeanFX2.FX1
