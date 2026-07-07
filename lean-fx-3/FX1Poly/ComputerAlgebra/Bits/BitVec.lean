import FX1Poly.ComputerAlgebra.Number.NatModularReduction

/-! # BitVec — the fixed-width machine-integer substrate (hardware floor)

The zero-axiom bit-vector carrier for the register-layout / fixed-width tower /
ISA substrate (polycell §3.15 prereq).  Carrier is core Lean `BitVec width`
(`Fin (2^width)` under the hood); its `DecidableEq`, `toNat`, `ofNatLT`,
`eq_of_toNat_eq`, and the `isLt` bound are all axiom-clean (checked), so we get
GENUINE `Eq` — no setoid, no `Quot`.

The one thing core `BitVec` cannot give us zero-axiom is its ARITHMETIC and
BITWISE surface: `BitVec.add`/`mul` and `BitVec.and`/`or`/`xor` route through
`Nat.mod` / `Nat.land` whose reasoning lemmas are propext-poisoned.  So we define
OUR OWN operations:

* arithmetic reduces `mod 2^width` through the structural `natRemainder`
  (`NatModularReduction`) — "add/mul in `Nat`, then reduce", never Init `%`;
* bitwise logic is a structural per-bit fold over `Bool` (never `Nat.land` /
  `Nat.testBit`, both propext-dirty) — bit access is `natRemainder (v >>> i) 2`,
  built only on the structural `Nat.shiftRight`;
* shifts / concat / slice / extend are pure `Nat.shiftLeft`/`shiftRight`/`pow`/
  arithmetic wrapped by the `mod 2^width` reducer;
* signed interpretation `bitVecToInt` is a clean two's-complement `Int` fold.

`Init`-only, structural (no well-founded recursion), zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Reduction into a fixed width -/

/-- `value` reduced `mod 2^width` into `BitVec width`, via the structural
`natRemainder` and the `ofNatLT` (no-mod) constructor. -/
def bitVecOfNatMod {width : Nat} (value : Nat) : BitVec width :=
  BitVec.ofNatLT (natRemainder value (2 ^ width)) (natRemainderIsBounded (Nat.two_pow_pos width))

/-- The reducer's underlying natural is exactly the structural remainder. -/
theorem bitVecOfNatModToNat {width : Nat} (value : Nat) :
    (bitVecOfNatMod (width := width) value).toNat = natRemainder value (2 ^ width) :=
  BitVec.toNat_ofNatLT _ _

/-! ## Constants -/

/-- The all-zero vector. -/
def bitVecZero {width : Nat} : BitVec width :=
  BitVec.ofNatLT 0 (Nat.two_pow_pos width)

/-- The unit vector (`1` reduced `mod 2^width`; degenerates to `0` at width 0). -/
def bitVecOne {width : Nat} : BitVec width :=
  bitVecOfNatMod 1

@[simp] theorem bitVecZeroToNat {width : Nat} : (bitVecZero (width := width)).toNat = 0 :=
  BitVec.toNat_ofNatLT _ _

/-! ## Modular arithmetic (add / neg / sub / mul) -/

/-- Modular addition. -/
def bitVecAdd {width : Nat} (left right : BitVec width) : BitVec width :=
  bitVecOfNatMod (left.toNat + right.toNat)

/-- Modular multiplication. -/
def bitVecMul {width : Nat} (left right : BitVec width) : BitVec width :=
  bitVecOfNatMod (left.toNat * right.toNat)

/-- Modular negation — the two's-complement complement `2^width - value`. -/
def bitVecNeg {width : Nat} (value : BitVec width) : BitVec width :=
  bitVecOfNatMod (2 ^ width - value.toNat)

/-- Modular subtraction, as addition of the complement. -/
def bitVecSub {width : Nat} (left right : BitVec width) : BitVec width :=
  bitVecAdd left (bitVecNeg right)

theorem bitVecAddToNat {width : Nat} (left right : BitVec width) :
    (bitVecAdd left right).toNat = natRemainder (left.toNat + right.toNat) (2 ^ width) :=
  bitVecOfNatModToNat _

theorem bitVecMulToNat {width : Nat} (left right : BitVec width) :
    (bitVecMul left right).toNat = natRemainder (left.toNat * right.toNat) (2 ^ width) :=
  bitVecOfNatModToNat _

theorem bitVecNegToNat {width : Nat} (value : BitVec width) :
    (bitVecNeg value).toNat = natRemainder (2 ^ width - value.toNat) (2 ^ width) :=
  bitVecOfNatModToNat _

/-! ## Decidable equality (genuine `Eq` on the core carrier) -/

/-- Structural decidable equality on `BitVec width` (core, axiom-clean). -/
def bitVecDecidableEq {width : Nat} : DecidableEq (BitVec width) := inferInstance

/-! ## Structural per-bit access -/

/-- Bit `index` of `value` as a `Bool`, via the structural `Nat.shiftRight` and the
counting remainder — no `Nat.land` / `Nat.testBit`. -/
def bitAtNat (value index : Nat) : Bool :=
  ! (natRemainder (value >>> index) 2 == 0)

/-- Contribution of bit `position` to a natural: `2^position` when set. -/
def bitWeight (isSet : Bool) (position : Nat) : Nat :=
  if isSet then 2 ^ position else 0

/-! ## Bitwise logic (structural fold, never `Nat.land`) -/

/-- Fold a binary bit-combiner over positions `0 .. count-1`, LSB-first. -/
def bitwiseFold (combine : Bool → Bool → Bool) (left right : Nat) : Nat → Nat
  | 0 => 0
  | position + 1 =>
      bitwiseFold combine left right position +
        bitWeight (combine (bitAtNat left position) (bitAtNat right position)) position

/-- Fold a unary bit-combiner over positions `0 .. count-1`, LSB-first. -/
def bitwiseUnaryFold (combine : Bool → Bool) (source : Nat) : Nat → Nat
  | 0 => 0
  | position + 1 =>
      bitwiseUnaryFold combine source position +
        bitWeight (combine (bitAtNat source position)) position

/-- Bitwise AND. -/
def bitVecAnd {width : Nat} (left right : BitVec width) : BitVec width :=
  bitVecOfNatMod (bitwiseFold and left.toNat right.toNat width)

/-- Bitwise OR. -/
def bitVecOr {width : Nat} (left right : BitVec width) : BitVec width :=
  bitVecOfNatMod (bitwiseFold or left.toNat right.toNat width)

/-- Bitwise XOR. -/
def bitVecXor {width : Nat} (left right : BitVec width) : BitVec width :=
  bitVecOfNatMod (bitwiseFold (fun leftBit rightBit => leftBit != rightBit)
    left.toNat right.toNat width)

/-- Bitwise NOT (one's complement within the width). -/
def bitVecNot {width : Nat} (value : BitVec width) : BitVec width :=
  bitVecOfNatMod (bitwiseUnaryFold (fun bit => !bit) value.toNat width)

/-! ## Shifts -/

/-- Logical left shift by `amount`, truncating to the width. -/
def bitVecShl {width : Nat} (value : BitVec width) (amount : Nat) : BitVec width :=
  bitVecOfNatMod (value.toNat <<< amount)

/-- Logical right shift by `amount` (zero-fill). -/
def bitVecShr {width : Nat} (value : BitVec width) (amount : Nat) : BitVec width :=
  bitVecOfNatMod (value.toNat >>> amount)

/-- The top (sign) bit is set iff `2 * value ≥ 2^width`. -/
def bitVecIsNegative {width : Nat} (value : BitVec width) : Bool :=
  ! (2 * value.toNat < 2 ^ width)

/-- Arithmetic right shift by `amount` (sign-fill): the vacated high bits copy the
sign bit, expressed as adding the top-`amount` mask when the sign bit is set. -/
def bitVecAshr {width : Nat} (value : BitVec width) (amount : Nat) : BitVec width :=
  if bitVecIsNegative value then
    bitVecOfNatMod ((value.toNat >>> amount) + (2 ^ width - 2 ^ (width - amount)))
  else
    bitVecOfNatMod (value.toNat >>> amount)

/-! ## Concatenation, slicing, extension -/

/-- LSB-first concatenation: `low` occupies bits `0 .. n-1`, `high` bits `n ..`. -/
def bitVecConcat {lowWidth highWidth : Nat}
    (low : BitVec lowWidth) (high : BitVec highWidth) : BitVec (lowWidth + highWidth) :=
  bitVecOfNatMod (low.toNat + high.toNat * 2 ^ lowWidth)

/-- Extract bits `[lo .. hi]` (inclusive) into a `BitVec (hi - lo + 1)`. -/
def bitVecExtract {width : Nat} (value : BitVec width) (hi lo : Nat) :
    BitVec (hi - lo + 1) :=
  bitVecOfNatMod (value.toNat >>> lo)

/-- Zero-extend (or truncate) to `newWidth`. -/
def bitVecZeroExtend {width : Nat} (value : BitVec width) (newWidth : Nat) :
    BitVec newWidth :=
  bitVecOfNatMod value.toNat

/-- Sign-extend to `newWidth`: replicate the sign bit into the new high bits. -/
def bitVecSignExtend {width : Nat} (value : BitVec width) (newWidth : Nat) :
    BitVec newWidth :=
  if bitVecIsNegative value then
    bitVecOfNatMod (value.toNat + (2 ^ newWidth - 2 ^ width))
  else
    bitVecOfNatMod value.toNat

/-! ## Signed interpretation (two's complement) -/

/-- Unsigned interpretation — the underlying natural. -/
def bitVecToNat {width : Nat} (value : BitVec width) : Nat := value.toNat

/-- Two's-complement signed interpretation into `Int`: the sign bit carries weight
`-2^width`, all lower bits positive.  Fully clean (`Int.ofNat`/`Int.sub`). -/
def bitVecToInt {width : Nat} (value : BitVec width) : Int :=
  if bitVecIsNegative value then
    Int.ofNat value.toNat - Int.ofNat (2 ^ width)
  else
    Int.ofNat value.toNat

end FX1Poly.ComputerAlgebra
