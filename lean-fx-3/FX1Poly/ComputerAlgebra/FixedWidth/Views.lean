import FX1Poly.ComputerAlgebra.Bits.BitVec
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra

/-! # FixedWidth/Views — the `uN` / `iN` machine-integer facades

FX §3.1's `u8 .. u1024` (unsigned) and `i8 .. i1024` (signed two's complement)
share one carrier `BitVec width` (genuine `Eq`): two's-complement arithmetic is
bit-identical to unsigned `mod 2^n`, so one `bitVecCommutativeRingWitness` backs
both.  One-field wrappers `UIntN` / `SIntN` (not a defeq `abbrev`) keep the
families nominally distinct, equality `congrArg` on `bits`.  Readouts: unsigned
`bits.toNat` in `[0, 2^n)` (`BitVec.isLt`), signed `bitVecToInt bits` in
`[-2^(n-1), 2^(n-1))` (bound `sIntNValueIsBounded` in `FixedWidth/SignedSemantics`).
Arithmetic delegates to `Bits/BitVec` (wrap-by-default, FX `overflow(wrap)`); the
u/i split shows only in the sign-sensitive ops.

`Init`-only, structural, genuine-`Eq`, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The two nominal wrappers -/

/-- Unsigned fixed-width integer: `BitVec width` read via `bitVecToNat`. -/
structure UIntN (width : Nat) where
  bits : BitVec width

/-- Signed fixed-width integer: `BitVec width` read via `bitVecToInt`. -/
structure SIntN (width : Nat) where
  bits : BitVec width

/-! ## Nominal equality is genuine `Eq`: `congrArg` on `bits`, no setoid coarsening -/

theorem uIntNEqOfBitsEq {width : Nat} {left right : UIntN width}
    (bitsEqual : left.bits = right.bits) : left = right := by
  cases left; cases right; exact congrArg UIntN.mk bitsEqual

theorem sIntNEqOfBitsEq {width : Nat} {left right : SIntN width}
    (bitsEqual : left.bits = right.bits) : left = right := by
  cases left; cases right; exact congrArg SIntN.mk bitsEqual

/-! ## Constructors -/

/-- Unsigned view from a natural, reduced `mod 2^width`. -/
def UIntN.ofNat {width : Nat} (value : Nat) : UIntN width :=
  ⟨bitVecOfNatMod value⟩

/-- Signed view from a natural bit-pattern, reduced `mod 2^width`. -/
def SIntN.ofNat {width : Nat} (value : Nat) : SIntN width :=
  ⟨bitVecOfNatMod value⟩

def UIntN.zero {width : Nat} : UIntN width := ⟨bitVecZero⟩

def UIntN.one {width : Nat} : UIntN width := ⟨bitVecOne⟩

def SIntN.zero {width : Nat} : SIntN width := ⟨bitVecZero⟩

def SIntN.one {width : Nat} : SIntN width := ⟨bitVecOne⟩

/-! ## The value interpretations -/

/-- Unsigned interpretation: the underlying natural in `[0, 2^n)`. -/
def UIntN.unsignedValue {width : Nat} (value : UIntN width) : Nat :=
  value.bits.toNat

/-- Signed interpretation: the two's-complement integer. -/
def SIntN.signedValue {width : Nat} (value : SIntN width) : Int :=
  bitVecToInt value.bits

/-- Unsigned range is definitional: every value is below `2^n` (`BitVec.isLt`). -/
theorem uIntNValueIsBounded {width : Nat} (value : UIntN width) :
    value.unsignedValue < 2 ^ width :=
  value.bits.isLt

/-! ## Wrap-by-default arithmetic — bit-identical across the u/i split -/

def UIntN.add {width : Nat} (left right : UIntN width) : UIntN width :=
  ⟨bitVecAdd left.bits right.bits⟩

def UIntN.mul {width : Nat} (left right : UIntN width) : UIntN width :=
  ⟨bitVecMul left.bits right.bits⟩

def UIntN.sub {width : Nat} (left right : UIntN width) : UIntN width :=
  ⟨bitVecSub left.bits right.bits⟩

def SIntN.add {width : Nat} (left right : SIntN width) : SIntN width :=
  ⟨bitVecAdd left.bits right.bits⟩

def SIntN.mul {width : Nat} (left right : SIntN width) : SIntN width :=
  ⟨bitVecMul left.bits right.bits⟩

def SIntN.sub {width : Nat} (left right : SIntN width) : SIntN width :=
  ⟨bitVecSub left.bits right.bits⟩

/-- Two's-complement negation. -/
def SIntN.neg {width : Nat} (value : SIntN width) : SIntN width :=
  ⟨bitVecNeg value.bits⟩

/-! ## Sign-sensitive ops (the only place the u/i split shows) -/

/-- Unsigned right shift (logical, zero-fill). -/
def UIntN.shr {width : Nat} (value : UIntN width) (amount : Nat) : UIntN width :=
  ⟨bitVecShr value.bits amount⟩

/-- Signed right shift (arithmetic, sign-fill). -/
def SIntN.ashr {width : Nat} (value : SIntN width) (amount : Nat) : SIntN width :=
  ⟨bitVecAshr value.bits amount⟩

/-- Sign test on a signed view. -/
def SIntN.isNegative {width : Nat} (value : SIntN width) : Bool :=
  bitVecIsNegative value.bits

/-! ## Standard widths — the spec-canonical FX §3.1 primitive type names -/

abbrev u8 := UIntN 8
abbrev u16 := UIntN 16
abbrev u32 := UIntN 32
abbrev u64 := UIntN 64
abbrev u128 := UIntN 128
abbrev u256 := UIntN 256
abbrev u512 := UIntN 512
abbrev u1024 := UIntN 1024

abbrev i8 := SIntN 8
abbrev i16 := SIntN 16
abbrev i32 := SIntN 32
abbrev i64 := SIntN 64
abbrev i128 := SIntN 128
abbrev i256 := SIntN 256
abbrev i512 := SIntN 512
abbrev i1024 := SIntN 1024

end FX1Poly.ComputerAlgebra
