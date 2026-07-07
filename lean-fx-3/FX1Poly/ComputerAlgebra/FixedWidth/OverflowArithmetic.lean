import FX1Poly.ComputerAlgebra.Bits.BitVecRing
import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision

/-! # FixedWidth/OverflowArithmetic — wrap / trap / saturate (dim 16)

The three non-`exact` overflow modes of FX §6.3 dim 16 as typed operations on the
shipped `BitVec` substrate, each with proven semantics.  The overflow TEST is the
STRUCTURAL `Nat` order on the un-reduced true sum/product `a.toNat (+/*) b.toNat`
via `Nat.blt` (a `Bool` program, `propext`-clean) — never a `shiftRight`/`div`
bit comparison, which would leak `propext`.

* **wrap** — `bitVecAdd`/`bitVecMul` are ALREADY the `mod 2^n` ops; the wrap
  result is exactly `(a (+/*) b) mod 2^n` (`bitVecAddToNat`, re-exported).  The
  wrap algebra IS the shipped `bitVecCommutativeRingWitness`.
* **trap** — `Option`; `some (reduced result)` iff the true result FITS below
  `2^n`, `none` on overflow.  On the fits domain trap agrees with wrap.
* **saturate** — clamps to the top value `2^n − 1` on overflow, the exact reduced
  result otherwise.

Unsigned add and mul are covered for each mode.  Signed trap/saturate (target
window `[-2^(n-1), 2^(n-1))`, needing an `Int → BitVec` encoder + round-trip) are
the heavier signed follow-on brick.

`Init`-only, structural, genuine-`Eq`, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Order-to-`Bool` bridges for the overflow test -/

/-- `low < high` forces the `Nat.blt` flag `true`. -/
theorem natBltEqTrueOfLt {low high : Nat} (isBelow : low < high) :
    Nat.blt low high = true :=
  natBleEqTrueOfLe isBelow

/-- A strict-above witness forces `Nat.ble` `false` — structural double
recursion. -/
theorem natBleEqFalseOfLt : ∀ {highBound lowValue : Nat},
    lowValue < highBound → Nat.ble highBound lowValue = false
  | 0, _, isImpossible => nomatch isImpossible
  | _ + 1, 0, _ => rfl
  | highBound + 1, lowValue + 1, isBelow =>
      natBleEqFalseOfLt (highBound := highBound) (lowValue := lowValue)
        (Nat.lt_of_succ_lt_succ isBelow)

/-- `high ≤ low` forces the `Nat.blt low high` flag `false`. -/
theorem natBltEqFalseOfLe {low high : Nat} (isNotBelow : high ≤ low) :
    Nat.blt low high = false :=
  natBleEqFalseOfLt (Nat.lt_succ_of_le isNotBelow)

/-! ## wrap — the shipped `mod 2^n` arithmetic -/

/-- Wrapping addition (FX `overflow(wrap)`). -/
def wrapAdd {width : Nat} (left right : BitVec width) : BitVec width :=
  bitVecAdd left right

/-- Wrapping multiplication. -/
def wrapMul {width : Nat} (left right : BitVec width) : BitVec width :=
  bitVecMul left right

/-- **Wrap add is the modular sum** `(a + b) mod 2^n`. -/
theorem wrapAddIsModularSum {width : Nat} (left right : BitVec width) :
    (wrapAdd left right).toNat = natRemainder (left.toNat + right.toNat) (2 ^ width) :=
  bitVecAddToNat left right

/-- **Wrap mul is the modular product** `(a * b) mod 2^n`. -/
theorem wrapMulIsModularProduct {width : Nat} (left right : BitVec width) :
    (wrapMul left right).toNat = natRemainder (left.toNat * right.toNat) (2 ^ width) :=
  bitVecMulToNat left right

/-! ## trap — `Option`, `some` iff the true result fits -/

/-- Trapping addition: `some` of the reduced sum when it fits below `2^n`, else
`none`. -/
def trapAdd {width : Nat} (left right : BitVec width) : Option (BitVec width) :=
  cond (Nat.blt (left.toNat + right.toNat) (2 ^ width))
    (some (bitVecOfNatMod (left.toNat + right.toNat)))
    none

/-- Trapping multiplication. -/
def trapMul {width : Nat} (left right : BitVec width) : Option (BitVec width) :=
  cond (Nat.blt (left.toNat * right.toNat) (2 ^ width))
    (some (bitVecOfNatMod (left.toNat * right.toNat)))
    none

/-- **Trap add returns `some` exactly on the fits domain**, and the payload is
the exact (un-wrapped) sum. -/
theorem trapAddFits {width : Nat} (left right : BitVec width)
    (fits : left.toNat + right.toNat < 2 ^ width) :
    trapAdd left right = some (bitVecOfNatMod (left.toNat + right.toNat)) :=
  congrArg
    (fun flag => cond flag (some (bitVecOfNatMod (left.toNat + right.toNat))) none)
    (natBltEqTrueOfLt fits)

/-- **Trap add returns `none` exactly on overflow.** -/
theorem trapAddOverflows {width : Nat} (left right : BitVec width)
    (overflows : 2 ^ width ≤ left.toNat + right.toNat) :
    trapAdd left right = none :=
  congrArg
    (fun flag => cond flag (some (bitVecOfNatMod (left.toNat + right.toNat))) none)
    (natBltEqFalseOfLe overflows)

/-- On the fits domain the trap payload is the EXACT sum (no wrap-around). -/
theorem trapAddSomeIsExact {width : Nat} (left right : BitVec width)
    (fits : left.toNat + right.toNat < 2 ^ width) :
    (bitVecOfNatMod (width := width) (left.toNat + right.toNat)).toNat
      = left.toNat + right.toNat :=
  (bitVecOfNatModToNat (left.toNat + right.toNat)).trans (natRemainderOfLt fits)

/-- The trap payload AGREES with the wrap result (both are the reduced sum). -/
theorem trapAddSomeAgreesWrap {width : Nat} (left right : BitVec width) :
    bitVecOfNatMod (width := width) (left.toNat + right.toNat) = wrapAdd left right :=
  rfl

/-- **Trap mul returns `some` exactly on the fits domain.** -/
theorem trapMulFits {width : Nat} (left right : BitVec width)
    (fits : left.toNat * right.toNat < 2 ^ width) :
    trapMul left right = some (bitVecOfNatMod (left.toNat * right.toNat)) :=
  congrArg
    (fun flag => cond flag (some (bitVecOfNatMod (left.toNat * right.toNat))) none)
    (natBltEqTrueOfLt fits)

/-- **Trap mul returns `none` exactly on overflow.** -/
theorem trapMulOverflows {width : Nat} (left right : BitVec width)
    (overflows : 2 ^ width ≤ left.toNat * right.toNat) :
    trapMul left right = none :=
  congrArg
    (fun flag => cond flag (some (bitVecOfNatMod (left.toNat * right.toNat))) none)
    (natBltEqFalseOfLe overflows)

/-! ## saturate — clamp to the top value on overflow -/

/-- The all-ones (maximum unsigned) value `2^n − 1`. -/
def bitVecMaxUnsigned {width : Nat} : BitVec width :=
  bitVecOfNatMod (2 ^ width - 1)

/-- `2^n − 1` is below `2^n`. -/
theorem maxUnsignedBelowModulus {width : Nat} : 2 ^ width - 1 < 2 ^ width :=
  let oneLe : 1 ≤ 2 ^ width := Nat.two_pow_pos width
  let reconstruct : 1 + (2 ^ width - 1) = 2 ^ width := natAddSubOfLe oneLe
  reconstruct ▸ (Nat.add_comm (2 ^ width - 1) 1 ▸ Nat.lt_succ_self (2 ^ width - 1))

/-- The max value reads back as `2^n − 1`. -/
theorem bitVecMaxUnsignedToNat {width : Nat} :
    (bitVecMaxUnsigned (width := width)).toNat = 2 ^ width - 1 :=
  (bitVecOfNatModToNat (2 ^ width - 1)).trans (natRemainderOfLt maxUnsignedBelowModulus)

/-- Saturating addition: the exact reduced sum when it fits, else clamp to
`2^n − 1`. -/
def saturateAddUnsigned {width : Nat} (left right : BitVec width) : BitVec width :=
  cond (Nat.blt (left.toNat + right.toNat) (2 ^ width))
    (bitVecOfNatMod (left.toNat + right.toNat))
    bitVecMaxUnsigned

/-- Saturating multiplication. -/
def saturateMulUnsigned {width : Nat} (left right : BitVec width) : BitVec width :=
  cond (Nat.blt (left.toNat * right.toNat) (2 ^ width))
    (bitVecOfNatMod (left.toNat * right.toNat))
    bitVecMaxUnsigned

/-- **In range, saturate add is the exact sum.** -/
theorem saturateAddInRange {width : Nat} (left right : BitVec width)
    (fits : left.toNat + right.toNat < 2 ^ width) :
    (saturateAddUnsigned left right).toNat = left.toNat + right.toNat :=
  (congrArg
      (fun flag =>
        (cond flag (bitVecOfNatMod (left.toNat + right.toNat)) bitVecMaxUnsigned).toNat)
      (natBltEqTrueOfLt fits)).trans
    ((bitVecOfNatModToNat (left.toNat + right.toNat)).trans (natRemainderOfLt fits))

/-- **On overflow, saturate add clamps to `2^n − 1`.** -/
theorem saturateAddClamps {width : Nat} (left right : BitVec width)
    (overflows : 2 ^ width ≤ left.toNat + right.toNat) :
    (saturateAddUnsigned left right).toNat = 2 ^ width - 1 :=
  (congrArg
      (fun flag =>
        (cond flag (bitVecOfNatMod (left.toNat + right.toNat)) bitVecMaxUnsigned).toNat)
      (natBltEqFalseOfLe overflows)).trans
    bitVecMaxUnsignedToNat

/-- A value strictly below a bound is at most the bound's predecessor. -/
theorem natLeSubOneOfLt {value bound : Nat} (isBelow : value < bound) :
    value ≤ bound - 1 :=
  let oneLe : 1 ≤ bound := Nat.lt_of_le_of_lt (Nat.zero_le value) isBelow
  let reconstruct : (bound - 1) + 1 = bound :=
    (Nat.add_comm (bound - 1) 1).trans (natAddSubOfLe oneLe)
  Nat.le_of_succ_le_succ (reconstruct.symm ▸ isBelow)

/-- **Saturate add is upper-bounded by `2^n − 1`** on both branches (clamp
correctness). -/
theorem saturateAddUpperBounded {width : Nat} (left right : BitVec width) :
    (saturateAddUnsigned left right).toNat ≤ 2 ^ width - 1 :=
  match Nat.lt_or_ge (left.toNat + right.toNat) (2 ^ width) with
  | .inl fits =>
      Nat.le_trans (Nat.le_of_eq (saturateAddInRange left right fits))
        (natLeSubOneOfLt fits)
  | .inr overflows => Nat.le_of_eq (saturateAddClamps left right overflows)

end FX1Poly.ComputerAlgebra
