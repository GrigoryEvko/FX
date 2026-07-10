import FX1Poly.Polygraph.Omega.SteinerFoundation.CellCoordinates
import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore
import FX1Poly.ComputerAlgebra.Number.IntAddAssociativity

/-! # Polygraph/Omega/Steiner/CoordinateArithmetic — the abelian-group kit on equal-length chains
    (OMEGA-2 r1, the B-arith kit under the `isStrongSteiner` interface line)

The Steiner substrate (`Steiner/CellCoordinates.lean`) ships `addCoordinates` / `subtractCoordinates`
on `CellVector = List Int` with fully-enumerated (truncating) arms.  OMEGA-2's linearize soundness
fold needs the abelian-group laws of coordinate addition — commutativity, associativity, and a
zero identity — plus a length invariant so the truncating arithmetic is EXACT inside one dimension.
This file supplies exactly that kit, structurally, zero-axiom.

The three facts the CROWN soundness fold consumes:
  * `addCoordinates_comm`  — the Godement/interchange row (composition commutativity at disjoint
    top support) is literally `addCoordinates` commutativity.
  * `addCoordinates_assoc` — vertical-associativity is `addCoordinates` associativity.
  * `addCoordinates_zeroVector_left` / `_right` — the two unit rows are addition against the
    degenerate identity table `zeroVector` (identities are degenerate = zero top content).

Every proof is structural recursion on the coordinate lists over the zero-axiom Int lemmas
`intAddComm` / `intAddAssoc` / `intZeroAdd` / `intAddZero` (Init's `Int.add_comm` etc. are
propext-dirty — see `ComputerAlgebra/Number/IntArithmeticCore.lean`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Omega/Steiner/CoordinateArithmetic.lean`. -/

namespace FX1Poly.Polygraph.Steiner

open FX1Poly.ComputerAlgebra

/-! ## The degenerate identity table -/

/-- The all-zero coordinate vector of a given ambient length — the arithmetic image of an identity
cell (an identity contributes NO top-dimensional generator content).  Self-defined so its length
computes structurally. -/
def zeroVector : Nat → CellVector
  | 0 => []
  | count + 1 => 0 :: zeroVector count

/-- `zeroVector count` has length `count`. -/
theorem zeroVector_length : (count : Nat) → (zeroVector count).length = count
  | 0 => rfl
  | count + 1 => congrArg (· + 1) (zeroVector_length count)

/-! ## The nil absorbers (truncation on a ragged operand) -/

/-- `addCoordinates` with an empty LEFT operand truncates to empty. -/
theorem addCoordinates_nil_left : (rightVector : CellVector) → addCoordinates [] rightVector = []
  | [] => rfl
  | _ :: _ => rfl

/-- `addCoordinates` with an empty RIGHT operand truncates to empty. -/
theorem addCoordinates_nil_right : (leftVector : CellVector) → addCoordinates leftVector [] = []
  | [] => rfl
  | _ :: _ => rfl

/-! ## The abelian-group laws (unconditional; truncation is symmetric) -/

/-- **Coordinate addition commutes** — the interchange/Godement row on top support.  Unconditional:
the truncating arms are symmetric, and the cons arm commutes by `intAddComm`. -/
theorem addCoordinates_comm : (leftVector rightVector : CellVector) →
    addCoordinates leftVector rightVector = addCoordinates rightVector leftVector
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | leftHead :: leftTail, rightHead :: rightTail => by
      show (leftHead + rightHead) :: addCoordinates leftTail rightTail
        = (rightHead + leftHead) :: addCoordinates rightTail leftTail
      rw [intAddComm leftHead rightHead, addCoordinates_comm leftTail rightTail]

/-- **Coordinate addition associates** — the vertical-associativity row.  Unconditional: the
ragged base cases collapse through the nil absorbers, the cons arm associates by `intAddAssoc`. -/
theorem addCoordinates_assoc : (leftVector middleVector rightVector : CellVector) →
    addCoordinates (addCoordinates leftVector middleVector) rightVector
      = addCoordinates leftVector (addCoordinates middleVector rightVector)
  | [], _, _ => by
      rw [addCoordinates_nil_left, addCoordinates_nil_left, addCoordinates_nil_left]
  | _ :: _, [], _ => by
      rw [addCoordinates_nil_right, addCoordinates_nil_left, addCoordinates_nil_right]
  | _ :: _, _ :: _, [] => by
      rw [addCoordinates_nil_right, addCoordinates_nil_right, addCoordinates_nil_right]
  | leftHead :: leftTail, middleHead :: middleTail, rightHead :: rightTail => by
      show ((leftHead + middleHead) + rightHead)
          :: addCoordinates (addCoordinates leftTail middleTail) rightTail
        = (leftHead + (middleHead + rightHead))
          :: addCoordinates leftTail (addCoordinates middleTail rightTail)
      rw [intAddAssoc leftHead middleHead rightHead,
        addCoordinates_assoc leftTail middleTail rightTail]

/-! ## The length invariant (exactness inside one dimension) -/

/-- **Equal-length addition preserves length** — the exactness fact: adding two vectors of the same
length yields a vector of that length (no truncation fires).  Structural on the lists. -/
theorem addCoordinates_length_eq : (leftVector rightVector : CellVector) →
    leftVector.length = rightVector.length →
    (addCoordinates leftVector rightVector).length = leftVector.length
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], lengthsEqual => Nat.noConfusion lengthsEqual
  | leftHead :: leftTail, rightHead :: rightTail, lengthsEqual => by
      show (addCoordinates leftTail rightTail).length + 1 = leftTail.length + 1
      exact congrArg (· + 1)
        (addCoordinates_length_eq leftTail rightTail (Nat.succ.inj lengthsEqual))

/-! ## The zero identities (the two unit rows) -/

/-- **The degenerate identity table is a LEFT unit for coordinate addition** at its own length —
the left-unit row `id . a ~ a` in arithmetic form. -/
theorem addCoordinates_zeroVector_left : (vector : CellVector) →
    addCoordinates (zeroVector vector.length) vector = vector
  | [] => rfl
  | vectorHead :: vectorTail => by
      show (0 + vectorHead) :: addCoordinates (zeroVector vectorTail.length) vectorTail
        = vectorHead :: vectorTail
      rw [intZeroAdd vectorHead, addCoordinates_zeroVector_left vectorTail]

/-- **The degenerate identity table is a RIGHT unit for coordinate addition** at its own length —
the right-unit row `a . id ~ a` in arithmetic form. -/
theorem addCoordinates_zeroVector_right : (vector : CellVector) →
    addCoordinates vector (zeroVector vector.length) = vector
  | [] => rfl
  | vectorHead :: vectorTail => by
      show (vectorHead + 0) :: addCoordinates vectorTail (zeroVector vectorTail.length)
        = vectorHead :: vectorTail
      rw [intAddZero vectorHead, addCoordinates_zeroVector_right vectorTail]

/-! ## The degenerate shared boundary (the arithmetic form of `composeAtDimension` against an
identity) -/

/-- Negating the degenerate identity table leaves it unchanged (`-0 = 0` pointwise). -/
theorem negateCoordinates_zeroVector : (count : Nat) →
    negateCoordinates (zeroVector count) = zeroVector count
  | 0 => rfl
  | count + 1 => by
      show (-(0 : Int)) :: negateCoordinates (zeroVector count) = (0 : Int) :: zeroVector count
      rw [negateCoordinates_zeroVector count, intNegZero]

/-- **Subtracting the degenerate identity table is a no-op** at the vector's own length — so
`composeAtDimension left right ⟨zeroVector⟩` collapses to plain coordinate addition:
the shared boundary of a FREE composite is the degenerate (zero) identity table. -/
theorem subtractCoordinates_zeroVector_right : (vector : CellVector) →
    subtractCoordinates vector (zeroVector vector.length) = vector := by
  intro vector
  show addCoordinates vector (negateCoordinates (zeroVector vector.length)) = vector
  rw [negateCoordinates_zeroVector, addCoordinates_zeroVector_right]

end FX1Poly.Polygraph.Steiner
