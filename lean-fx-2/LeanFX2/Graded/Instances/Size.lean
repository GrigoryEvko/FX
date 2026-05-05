import LeanFX2.Graded.Instances.NatResource

/-! # Graded/Instances/Size — bounded-or-unbounded observation-depth semiring

`SizeGrade` tracks checked observation-depth bounds.  A bare `Nat` is not
faithful for FX because the language explicitly distinguishes bounded
observation-depth from `unbounded`.  The carrier is therefore `Nat ∪ {unbounded}`.

Operations:

* `0` = `bound 0`
* `1` = `bound 1`
* `+` = observation-depth-bound addition, with `unbounded` absorbing
* `*` = sequential scaling, with zero annihilating and nonzero
  unbounded scaling remaining unbounded
* `≤` = natural order extended with `unbounded` as top

This is a conservative v0.5 model of codata size: finite observations
remain natural bounds, while whole streams and other indefinitely
observable codata can be assigned `unbounded`.  It is materially
stronger than the old Nat wrapper because it represents the
spec-mandated unbounded case and keeps the semiring laws honest.

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Size grade: finite natural bound or unbounded observation-depth. -/
inductive SizeGrade : Type
  /-- A checked finite observation-depth bound. -/
  | bound (limit : Nat)
  /-- Explicitly unbounded observation-depth. -/
  | unbounded
  deriving DecidableEq, Repr

namespace SizeGrade

/-- Parallel composition adds finite bounds; unbounded absorbs. -/
def add : SizeGrade → SizeGrade → SizeGrade
  | .unbounded, _ => .unbounded
  | _, .unbounded => .unbounded
  | .bound leftBound, .bound rightBound => .bound (leftBound + rightBound)

/-- Sequential scaling multiplies finite bounds.  Zero annihilates,
including against an unbounded factor. -/
def mul : SizeGrade → SizeGrade → SizeGrade
  | .bound leftBound, .bound rightBound => .bound (leftBound * rightBound)
  | .bound 0, .unbounded => .bound 0
  | .bound (Nat.succ _), .unbounded => .unbounded
  | .unbounded, .bound 0 => .bound 0
  | .unbounded, .bound (Nat.succ _) => .unbounded
  | .unbounded, .unbounded => .unbounded

/-- Bound subsumption, with `unbounded` as top. -/
def le : SizeGrade → SizeGrade → Prop
  | _, .unbounded => True
  | .unbounded, .bound _ => False
  | .bound leftBound, .bound rightBound => leftBound ≤ rightBound

/-- Addition is associative. -/
theorem add_assoc : ∀ first second third,
    add (add first second) third = add first (add second third)
  | .bound firstBound, .bound secondBound, .bound thirdBound =>
      congrArg bound (Nat.add_assoc firstBound secondBound thirdBound)
  | .bound _, .bound _, .unbounded => rfl
  | .bound _, .unbounded, .bound _ => rfl
  | .bound _, .unbounded, .unbounded => rfl
  | .unbounded, .bound _, .bound _ => rfl
  | .unbounded, .bound _, .unbounded => rfl
  | .unbounded, .unbounded, .bound _ => rfl
  | .unbounded, .unbounded, .unbounded => rfl

/-- Addition is commutative. -/
theorem add_comm : ∀ first second, add first second = add second first
  | .bound firstBound, .bound secondBound =>
      congrArg bound (Nat.add_comm firstBound secondBound)
  | .bound _, .unbounded => rfl
  | .unbounded, .bound _ => rfl
  | .unbounded, .unbounded => rfl

/-- Left additive identity. -/
theorem add_zero_left : ∀ value, add (.bound 0) value = value
  | .bound valueBound => congrArg bound (Nat.zero_add valueBound)
  | .unbounded => rfl

/-- Right additive identity. -/
theorem add_zero_right : ∀ value, add value (.bound 0) = value
  | .bound valueBound => congrArg bound (Nat.add_zero valueBound)
  | .unbounded => rfl

/-- Multiplication is associative. -/
theorem mul_assoc : ∀ first second third,
    mul (mul first second) third = mul first (mul second third)
  | .bound firstBound, .bound secondBound, .bound thirdBound =>
      congrArg bound
        (NatResource.mulAssocClean
          firstBound secondBound thirdBound)
  | .bound 0, .bound 0, .unbounded => rfl
  | .bound 0, .bound (Nat.succ secondBound), .unbounded => by
      change mul (bound (0 * Nat.succ secondBound)) unbounded = bound 0
      rw [Nat.zero_mul]
      rfl
  | .bound (Nat.succ _), .bound 0, .unbounded => rfl
  | .bound (Nat.succ _), .bound (Nat.succ _), .unbounded => rfl
  | .bound 0, .unbounded, .bound 0 => rfl
  | .bound 0, .unbounded, .bound (Nat.succ thirdBound) => by
      change bound (0 * Nat.succ thirdBound) = bound 0
      rw [Nat.zero_mul]
  | .bound (Nat.succ _), .unbounded, .bound 0 => rfl
  | .bound (Nat.succ _), .unbounded, .bound (Nat.succ _) => rfl
  | .bound 0, .unbounded, .unbounded => rfl
  | .bound (Nat.succ _), .unbounded, .unbounded => rfl
  | .unbounded, .bound 0, .bound 0 => rfl
  | .unbounded, .bound 0, .bound (Nat.succ thirdBound) => by
      change .bound (0 * Nat.succ thirdBound) =
        mul .unbounded (.bound (0 * Nat.succ thirdBound))
      rw [Nat.zero_mul]
      rfl
  | .unbounded, .bound (Nat.succ _), .bound 0 => rfl
  | .unbounded, .bound (Nat.succ _), .bound (Nat.succ _) => rfl
  | .unbounded, .bound 0, .unbounded => rfl
  | .unbounded, .bound (Nat.succ _), .unbounded => rfl
  | .unbounded, .unbounded, .bound 0 => rfl
  | .unbounded, .unbounded, .bound (Nat.succ _) => rfl
  | .unbounded, .unbounded, .unbounded => rfl

/-- Left multiplicative identity. -/
theorem mul_one_left : ∀ value, mul (.bound 1) value = value
  | .bound 0 => rfl
  | .bound (Nat.succ valueBound) => congrArg bound (Nat.one_mul (Nat.succ valueBound))
  | .unbounded => rfl

/-- Right multiplicative identity. -/
theorem mul_one_right : ∀ value, mul value (.bound 1) = value
  | .bound 0 => rfl
  | .bound (Nat.succ valueBound) => congrArg bound (Nat.mul_one (Nat.succ valueBound))
  | .unbounded => rfl

/-- Left distributivity. -/
theorem mul_distrib_left : ∀ scalar leftAddend rightAddend,
    mul scalar (add leftAddend rightAddend) =
      add (mul scalar leftAddend) (mul scalar rightAddend)
  | .bound scalarBound, .bound leftBound, .bound rightBound =>
      congrArg bound
        (Nat.left_distrib scalarBound leftBound rightBound)
  | .bound 0, .bound leftBound, .unbounded => by
      change .bound 0 = add (.bound (0 * leftBound)) (.bound 0)
      rw [Nat.zero_mul]
      rfl
  | .bound (Nat.succ _), .bound _, .unbounded => rfl
  | .bound 0, .unbounded, .bound 0 => rfl
  | .bound 0, .unbounded, .bound (Nat.succ rightBound) => by
      change .bound 0 =
        add (.bound 0) (.bound (0 * Nat.succ rightBound))
      rw [Nat.zero_mul]
      rfl
  | .bound (Nat.succ _), .unbounded, .bound _ => rfl
  | .bound 0, .unbounded, .unbounded => rfl
  | .bound (Nat.succ _), .unbounded, .unbounded => rfl
  | .unbounded, .bound 0, .bound 0 => rfl
  | .unbounded, .bound 0, .bound (Nat.succ _) => rfl
  | .unbounded, .bound (Nat.succ _), .bound 0 => rfl
  | .unbounded, .bound (Nat.succ _), .bound (Nat.succ _) => rfl
  | .unbounded, .bound 0, .unbounded => rfl
  | .unbounded, .bound (Nat.succ _), .unbounded => rfl
  | .unbounded, .unbounded, .bound 0 => rfl
  | .unbounded, .unbounded, .bound (Nat.succ _) => rfl
  | .unbounded, .unbounded, .unbounded => rfl

/-- Right distributivity. -/
theorem mul_distrib_right : ∀ leftAddend rightAddend scalar,
    mul (add leftAddend rightAddend) scalar =
      add (mul leftAddend scalar) (mul rightAddend scalar)
  | .bound leftBound, .bound rightBound, .bound scalarBound =>
      congrArg bound
        (NatResource.mulRightDistribClean leftBound rightBound scalarBound)
  | .bound 0, .bound 0, .unbounded => rfl
  | .bound 0, .bound (Nat.succ _), .unbounded => rfl
  | .bound (Nat.succ leftBound), .bound 0, .unbounded => by
      change mul (.bound (Nat.succ leftBound + 0)) .unbounded = .unbounded
      rw [Nat.add_zero]
      rfl
  | .bound (Nat.succ _), .bound (Nat.succ _), .unbounded => rfl
  | .bound _, .unbounded, .bound 0 => rfl
  | .bound _, .unbounded, .bound (Nat.succ _) => rfl
  | .bound 0, .unbounded, .unbounded => rfl
  | .bound (Nat.succ _), .unbounded, .unbounded => rfl
  | .unbounded, .bound _, .bound 0 => rfl
  | .unbounded, .bound _, .bound (Nat.succ _) => rfl
  | .unbounded, .bound _, .unbounded => rfl
  | .unbounded, .unbounded, .bound 0 => rfl
  | .unbounded, .unbounded, .bound (Nat.succ _) => rfl
  | .unbounded, .unbounded, .unbounded => rfl

/-- Left zero annihilation. -/
theorem mul_zero_left : ∀ value, mul (.bound 0) value = .bound 0
  | .bound valueBound => congrArg bound (Nat.zero_mul valueBound)
  | .unbounded => rfl

/-- Right zero annihilation. -/
theorem mul_zero_right : ∀ value, mul value (.bound 0) = .bound 0
  | .bound valueBound => congrArg bound (Nat.mul_zero valueBound)
  | .unbounded => rfl

/-- Reflexivity of bound subsumption. -/
theorem le_refl : ∀ value, le value value
  | .bound valueBound => Nat.le_refl valueBound
  | .unbounded => True.intro

/-- A product is zero-bounded when the left factor is zero-bounded. -/
theorem mul_le_zero_of_left_le_zero
    {leftBound rightBound : Nat}
    (leftLeqZero : leftBound ≤ 0) :
    leftBound * rightBound ≤ 0 := by
  rw [← Nat.zero_mul rightBound]
  exact Nat.mul_le_mul leftLeqZero (Nat.le_refl rightBound)

/-- A product is zero-bounded when the right factor is zero-bounded. -/
theorem mul_le_zero_of_right_le_zero
    {leftBound rightBound : Nat}
    (rightLeqZero : rightBound ≤ 0) :
    leftBound * rightBound ≤ 0 := by
  rw [← Nat.mul_zero leftBound]
  exact Nat.mul_le_mul (Nat.le_refl leftBound) rightLeqZero

/-- Transitivity of bound subsumption. -/
theorem le_trans : ∀ first second third,
    le first second → le second third → le first third
  | .bound _, .bound _, .unbounded, _, _ => True.intro
  | .bound _firstBound, .bound _secondBound, .bound _thirdBound, firstLeSecond, secondLeThird =>
      Nat.le_trans firstLeSecond secondLeThird
  | .bound _, .unbounded, .unbounded, _, _ => True.intro
  | .unbounded, .unbounded, .unbounded, _, _ => True.intro

/-- Addition is monotone. -/
theorem add_mono : ∀ leftLow leftHigh rightLow rightHigh,
    le leftLow leftHigh → le rightLow rightHigh →
      le (add leftLow rightLow) (add leftHigh rightHigh)
  | .bound _, .bound _, .bound _, .unbounded, _, _ => True.intro
  | .bound _, .unbounded, .bound _, .bound _, _, _ => True.intro
  | .bound _, .unbounded, .bound _, .unbounded, _, _ => True.intro
  | .bound _leftLowBound, .bound _leftHighBound,
      .bound _rightLowBound, .bound _rightHighBound, leftLeq, rightLeq =>
      Nat.add_le_add leftLeq rightLeq
  | .bound _, .bound _, .unbounded, .unbounded, _, _ => True.intro
  | .bound _, .unbounded, .unbounded, .unbounded, _, _ => True.intro
  | .unbounded, .unbounded, .bound _, .bound _, _, _ => True.intro
  | .unbounded, .unbounded, .bound _, .unbounded, _, _ => True.intro
  | .unbounded, .unbounded, .unbounded, .unbounded, _, _ => True.intro

/-- Multiplication is monotone. -/
theorem mul_mono : ∀ leftLow leftHigh rightLow rightHigh,
    le leftLow leftHigh → le rightLow rightHigh →
      le (mul leftLow rightLow) (mul leftHigh rightHigh)
  | .bound leftLowBound, .bound 0, .bound rightLowBound, .unbounded, leftLeq, _ =>
      mul_le_zero_of_left_le_zero (leftBound := leftLowBound)
        (rightBound := rightLowBound) leftLeq
  | .bound _, .bound (Nat.succ _), .bound _, .unbounded, _, _ => True.intro
  | .bound leftLowBound, .unbounded, .bound rightLowBound, .bound 0, _, rightLeq =>
      mul_le_zero_of_right_le_zero (leftBound := leftLowBound)
        (rightBound := rightLowBound) rightLeq
  | .bound _, .unbounded, .bound _, .bound (Nat.succ _), _, _ => True.intro
  | .bound _, .unbounded, .bound _, .unbounded, _, _ => True.intro
  | .bound _leftLowBound, .bound _leftHighBound,
      .bound _rightLowBound, .bound _rightHighBound, leftLeq, rightLeq =>
      Nat.mul_le_mul leftLeq rightLeq
  | .bound 0, .bound 0, .unbounded, .unbounded, _, _ => Nat.le_refl 0
  | .bound 0, .bound (Nat.succ _), .unbounded, .unbounded, _, _ => True.intro
  | .bound (Nat.succ _), .bound 0, .unbounded, .unbounded, leftLeq, _ => by
      cases leftLeq
  | .bound (Nat.succ _), .bound (Nat.succ _), .unbounded, .unbounded, _, _ =>
      True.intro
  | .bound _, .unbounded, .unbounded, .unbounded, _, _ => True.intro
  | .unbounded, .unbounded, .bound 0, .bound 0, _, _ => Nat.le_refl 0
  | .unbounded, .unbounded, .bound 0, .bound (Nat.succ _), _, _ => True.intro
  | .unbounded, .unbounded, .bound (Nat.succ _), .bound 0, _, rightLeq => by
      cases rightLeq
  | .unbounded, .unbounded, .bound (Nat.succ _), .bound (Nat.succ _), _, _ =>
      True.intro
  | .unbounded, .unbounded, .bound _, .unbounded, _, _ => True.intro
  | .unbounded, .unbounded, .unbounded, .unbounded, _, _ => True.intro

end SizeGrade

/-- Size bounds form `WithTop Nat` under natural addition and
multiplication, with zero annihilating unbounded scaling. -/
instance : GradeSemiring SizeGrade where
  zero := .bound 0
  one  := .bound 1
  add  := SizeGrade.add
  mul  := SizeGrade.mul
  le   := SizeGrade.le

  add_assoc := SizeGrade.add_assoc
  add_comm := SizeGrade.add_comm
  add_zero_left := SizeGrade.add_zero_left
  add_zero_right := SizeGrade.add_zero_right
  mul_assoc := SizeGrade.mul_assoc
  mul_one_left := SizeGrade.mul_one_left
  mul_one_right := SizeGrade.mul_one_right
  mul_distrib_left := SizeGrade.mul_distrib_left
  mul_distrib_right := SizeGrade.mul_distrib_right
  mul_zero_left := SizeGrade.mul_zero_left
  mul_zero_right := SizeGrade.mul_zero_right
  le_refl := SizeGrade.le_refl
  le_trans := SizeGrade.le_trans
  add_mono := SizeGrade.add_mono
  mul_mono := SizeGrade.mul_mono

/-! ## Smoke samples -/

/-- Combining finite observation-depth witnesses adds their depths. -/
example :
    SizeGrade.add (.bound 2) (.bound 3) = .bound 5 := rfl

/-- Combining with unbounded observation-depth is unbounded. -/
example :
    SizeGrade.add (.bound 2) .unbounded = .unbounded := rfl

/-- Zero observation-depth annihilates an unbounded sequential factor. -/
example :
    SizeGrade.mul (.bound 0) .unbounded = .bound 0 := rfl

/-- Nonzero finite observation-depth times unbounded depth is unbounded. -/
example :
    SizeGrade.mul (.bound 2) .unbounded = .unbounded := rfl

end LeanFX2.Graded.Instances
