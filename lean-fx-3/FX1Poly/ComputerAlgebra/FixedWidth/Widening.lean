import FX1Poly.ComputerAlgebra.FixedWidth.Views
import FX1Poly.ComputerAlgebra.Bits.BitVecRing
import FX1Poly.ComputerAlgebra.Algebra.SetoidRingTower
import FX1Poly.ComputerAlgebra.Register.FieldLayout

/-! # FixedWidth/Widening — value-preserving widenings + the number-tower map

FX §3.8 makes `uN → uM` (zero-extend) an implicit lossless coercion, and reads a
fixed-width value out to `Nat` (`toNat`) or `Int` (`toInt`).  This module ships
the HONEST content of that request.

## The mathematical honesty note

Zero-extension, sign-extension, and the out-embeddings `toNat`/`toInt` are
**value-preserving sections, NOT ring homomorphisms.**  The source ring
`Z / 2^n Z` wraps at a
different modulus than the target, so widening does not commute with `add`
(e.g. in `Z/2`, `1 + 1 = 0`; zero-extended to `Z/4`, `1 + 1 = 2 ≠ 0`).  The
genuine ring/semiring homomorphism runs the OTHER way — it is the **reduction**
`Nat ↠ BitVec (width+1)`, the correct-direction number-tower arrow, whose
retraction the zero-extension provides.

So we deliver two distinct, both-true things:

1. **Value-preservation of zero-extension** — `zeroExtend` preserves `toNat` when
   the target is at least as wide (parameterised by `extra`, `newWidth =
   width + extra`, to keep the pow bound structural), plus the `UIntN` view form.
2. **The genuine tower hom** `reduceNatToBitVec : Nat ↠ BitVec (width+1)` as a
   `SetoidSemiringHom` into the shipped `bitVecCommutativeRingWitness` — the
   mirror of the shipped `embedNatToInt`, all five obligations from the modular
   corpus.  `preservesOne` is `rfl` (the unit is defined as `bitVecOfNatMod 1`).

Signed sign-extension value-preservation (`bitVecToInt`-preserving) and the
`Int ↠ BitVec` ring hom are the heavier signed follow-on brick (`negSucc` ↔
complement algebra); documented as the residual.

`Init`-only, genuine-`Eq`, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The pow widening bound -/

/-- A value below `2^width` stays below the wider modulus `2^(width+extra)`. -/
theorem valueBelowWiderModulus {width extra bound : Nat}
    (isBounded : bound < 2 ^ width) : bound < 2 ^ (width + extra) :=
  let widerFactored : 2 ^ (width + extra) = 2 ^ width * 2 ^ extra :=
    twoPowAdd 2 width extra
  let widthLeWider : 2 ^ width ≤ 2 ^ (width + extra) :=
    widerFactored.symm ▸ Nat.le_mul_of_pos_right (2 ^ width) (Nat.two_pow_pos extra)
  Nat.lt_of_lt_of_le isBounded widthLeWider

/-! ## (1) Zero-extension preserves the unsigned value -/

/-- **Widening zero-extension preserves `toNat`.**  `bitVecZeroExtend` reduces
`value.toNat` `mod 2^newWidth`; at a wider width the value is already below the
modulus, so the reduction is the identity. -/
theorem bitVecZeroExtendWideningPreservesToNat {width : Nat} (extra : Nat)
    (value : BitVec width) :
    (bitVecZeroExtend value (width + extra)).toNat = value.toNat :=
  (bitVecOfNatModToNat value.toNat).trans
    (natRemainderOfLt (valueBelowWiderModulus value.isLt))

/-- **Unsigned view widening** — zero-extend a `UIntN width` to `UIntN
(width + extra)`. -/
def UIntN.zeroExtend {width : Nat} (value : UIntN width) (extra : Nat) :
    UIntN (width + extra) :=
  ⟨bitVecZeroExtend value.bits (width + extra)⟩

/-- The widened unsigned view reads back the SAME unsigned value. -/
theorem uIntNZeroExtendPreservesValue {width : Nat} (value : UIntN width) (extra : Nat) :
    (value.zeroExtend extra).unsignedValue = value.unsignedValue :=
  bitVecZeroExtendWideningPreservesToNat extra value.bits

/-! ## (2) The genuine number-tower map: `Nat ↠ BitVec (width+1)`

The reduction `Nat ↠ Z/2^(width+1)` is a semiring homomorphism (like `ℕ ↪ ℤ`,
`Nat` has no negation).  The two operation obligations reduce, via `toNat`, to
"reduce-before-adding is invisible to the outer reduction" — the shipped
`natRemainderAddPush` / `natRemainderMulPush`. -/

/-- Reducing a sum equals adding the two reduced summands (the `bitVecAdd`
homomorphism law for the reducer). -/
theorem bitVecOfNatModAdd {width : Nat} (left right : Nat) :
    bitVecOfNatMod (width := width) (left + right)
      = bitVecAdd (bitVecOfNatMod left) (bitVecOfNatMod right) :=
  let modulus := 2 ^ width
  let positive : 0 < modulus := Nat.two_pow_pos width
  let chainForward :
      natRemainder (natRemainder left modulus + natRemainder right modulus) modulus
        = natRemainder (left + right) modulus :=
    (natRemainderAddPush left (natRemainder right modulus) modulus positive).trans
      ((congrArg (fun summed => natRemainder summed modulus)
          (Nat.add_comm left (natRemainder right modulus))).trans
        ((natRemainderAddPush right left modulus positive).trans
          (congrArg (fun summed => natRemainder summed modulus) (Nat.add_comm right left))))
  let rightToNat :
      (bitVecAdd (bitVecOfNatMod (width := width) left) (bitVecOfNatMod right)).toNat
        = natRemainder (natRemainder left modulus + natRemainder right modulus) modulus :=
    (bitVecAddToNat (bitVecOfNatMod left) (bitVecOfNatMod right)).trans
      ((congrArg (fun reduced => natRemainder (reduced + (bitVecOfNatMod right).toNat) modulus)
          (bitVecOfNatModToNat left)).trans
        (congrArg (fun reduced => natRemainder (natRemainder left modulus + reduced) modulus)
          (bitVecOfNatModToNat right)))
  BitVec.eq_of_toNat_eq
    ((bitVecOfNatModToNat (left + right)).trans (chainForward.symm.trans rightToNat.symm))

/-- Reducing a product equals multiplying the two reduced factors. -/
theorem bitVecOfNatModMul {width : Nat} (left right : Nat) :
    bitVecOfNatMod (width := width) (left * right)
      = bitVecMul (bitVecOfNatMod left) (bitVecOfNatMod right) :=
  let modulus := 2 ^ width
  let positive : 0 < modulus := Nat.two_pow_pos width
  let chainForward :
      natRemainder (natRemainder left modulus * natRemainder right modulus) modulus
        = natRemainder (left * right) modulus :=
    (natRemainderMulPush left (natRemainder right modulus) modulus positive).trans
      ((congrArg (fun scaled => natRemainder scaled modulus)
          (Nat.mul_comm left (natRemainder right modulus))).trans
        ((natRemainderMulPush right left modulus positive).trans
          (congrArg (fun scaled => natRemainder scaled modulus) (Nat.mul_comm right left))))
  let rightToNat :
      (bitVecMul (bitVecOfNatMod (width := width) left) (bitVecOfNatMod right)).toNat
        = natRemainder (natRemainder left modulus * natRemainder right modulus) modulus :=
    (bitVecMulToNat (bitVecOfNatMod left) (bitVecOfNatMod right)).trans
      ((congrArg (fun reduced => natRemainder (reduced * (bitVecOfNatMod right).toNat) modulus)
          (bitVecOfNatModToNat left)).trans
        (congrArg (fun reduced => natRemainder (natRemainder left modulus * reduced) modulus)
          (bitVecOfNatModToNat right)))
  BitVec.eq_of_toNat_eq
    ((bitVecOfNatModToNat (left * right)).trans (chainForward.symm.trans rightToNat.symm))

/-- The reducer sends `0` to the zero vector. -/
theorem bitVecOfNatModZero {width : Nat} :
    bitVecOfNatMod (width := width) 0 = bitVecZero :=
  BitVec.eq_of_toNat_eq
    ((bitVecOfNatModToNat 0).trans
      ((natRemainderOfLt (Nat.two_pow_pos width)).trans bitVecZeroToNat.symm))

/-- **`Nat ↠ BitVec (width+1)`** — the number-tower reduction as a genuine
setoid semiring homomorphism into the shipped commutative-ring witness.  This is
the honest, correct-direction fixed-width tower map (mirror of `embedNatToInt`).
`preservesOne` is `rfl` because `bitVecOne := bitVecOfNatMod 1`. -/
def reduceNatToBitVec (width : Nat) :
    SetoidSemiringHom natCommutativeSemiringWitness
      (commutativeSemiringWitnessOfRing (bitVecCommutativeRingWitness width)) where
  map := bitVecOfNatMod (width := width + 1)
  respectsDenotesSame := fun _ _ areEqual => congrArg bitVecOfNatMod areEqual
  preservesAdd := fun left right => bitVecOfNatModAdd left right
  preservesMul := fun left right => bitVecOfNatModMul left right
  preservesZero := bitVecOfNatModZero
  preservesOne := rfl

end FX1Poly.ComputerAlgebra
