import FX1Poly.ComputerAlgebra.Bits.BitVec
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra

/-! # FixedWidth/Views — the `uN` / `iN` machine-integer facades (dim 16 floor)

FX §3.1 exposes two fixed-width integer families over one bit substrate:
`u8 .. u1024` (unsigned) and `i8 .. i1024` (signed two's complement).  The
insight (confirmed against `Bits/BitVec`) is that these are NOT two carriers —
they are ONE carrier (`BitVec width`, genuine `Eq`) read through two different
INTERPRETATIONS, because two's-complement arithmetic is bit-identical to
unsigned `mod 2^n` arithmetic (which is exactly why a single
`bitVecCommutativeRingWitness` backs both).

So a view is a *(carrier, interpretation)* pair.  We make the two families
NOMINALLY distinct with one-field wrappers (`UIntN` / `SIntN`): a bare `abbrev`
would be defeq and could silently host cross-family mixing.  The wrap/unwrap
erases at runtime; equality on the wrapper is `congrArg` on the `bits` field, so
it stays genuine `Eq`.

* Unsigned readout: `UIntN.unsignedValue = bits.toNat`, range `[0, 2^n)` — the
  bound is DEFINITIONAL (`BitVec.isLt`), zero proof obligation.
* Signed readout: `SIntN.signedValue = bitVecToInt bits`, range
  `[-2^(n-1), 2^(n-1))` — one genuine case-split lemma (`signedValue`
  bounds, `width + 1` indexed so `n ≥ 1`): `sIntNValueIsBounded`, shipped in `FixedWidth/SignedSemantics`.

Arithmetic delegates to the shipped `Bits/BitVec` ops (wrap-by-default =
FX `overflow(wrap)`); the u/i split shows only in the sign-sensitive ops
(shr vs ashr, zero-extend vs sign-extend) and the interpretation.

`Init`-only, structural, genuine-`Eq`, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The two nominal wrappers -/

/-- **Unsigned fixed-width integer** — a `BitVec width` read via `bitVecToNat`. -/
structure UIntN (width : Nat) where
  bits : BitVec width

/-- **Signed fixed-width integer** — a `BitVec width` read via `bitVecToInt`
(two's complement). -/
structure SIntN (width : Nat) where
  bits : BitVec width

/-! ## Nominal equality stays genuine `Eq`

The wrapper injects/projects the single `bits` field, so equality of views is
equality of bits under `congrArg`, never a setoid coarsening. -/

/-- Two unsigned views are equal when their bits are. -/
theorem uIntNEqOfBitsEq {width : Nat} {left right : UIntN width}
    (bitsEqual : left.bits = right.bits) : left = right := by
  cases left; cases right; exact congrArg UIntN.mk bitsEqual

/-- Two signed views are equal when their bits are. -/
theorem sIntNEqOfBitsEq {width : Nat} {left right : SIntN width}
    (bitsEqual : left.bits = right.bits) : left = right := by
  cases left; cases right; exact congrArg SIntN.mk bitsEqual

/-! ## Constructors -/

/-- Build an unsigned view from a natural, reducing `mod 2^width`. -/
def UIntN.ofNat {width : Nat} (value : Nat) : UIntN width :=
  ⟨bitVecOfNatMod value⟩

/-- Build a signed view from a natural bit-pattern, reducing `mod 2^width`. -/
def SIntN.ofNat {width : Nat} (value : Nat) : SIntN width :=
  ⟨bitVecOfNatMod value⟩

/-- The unsigned zero. -/
def UIntN.zero {width : Nat} : UIntN width := ⟨bitVecZero⟩

/-- The unsigned one. -/
def UIntN.one {width : Nat} : UIntN width := ⟨bitVecOne⟩

/-- The signed zero. -/
def SIntN.zero {width : Nat} : SIntN width := ⟨bitVecZero⟩

/-- The signed one. -/
def SIntN.one {width : Nat} : SIntN width := ⟨bitVecOne⟩

/-! ## The value interpretations -/

/-- **Unsigned interpretation** — the underlying natural in `[0, 2^n)`. -/
def UIntN.unsignedValue {width : Nat} (value : UIntN width) : Nat :=
  value.bits.toNat

/-- **Signed interpretation** — the two's-complement integer. -/
def SIntN.signedValue {width : Nat} (value : SIntN width) : Int :=
  bitVecToInt value.bits

/-- **Unsigned range is definitional** — every unsigned value is below `2^n`,
straight from the carrier's `isLt` (which is `Fin.isLt`).  No proof obligation
beyond unfolding. -/
theorem uIntNValueIsBounded {width : Nat} (value : UIntN width) :
    value.unsignedValue < 2 ^ width :=
  value.bits.isLt

/-! ## Wrap-by-default arithmetic (delegates to the shipped `BitVec` ring) -/

/-- Unsigned addition (wraps `mod 2^n`). -/
def UIntN.add {width : Nat} (left right : UIntN width) : UIntN width :=
  ⟨bitVecAdd left.bits right.bits⟩

/-- Unsigned multiplication (wraps `mod 2^n`). -/
def UIntN.mul {width : Nat} (left right : UIntN width) : UIntN width :=
  ⟨bitVecMul left.bits right.bits⟩

/-- Unsigned subtraction (wraps `mod 2^n`). -/
def UIntN.sub {width : Nat} (left right : UIntN width) : UIntN width :=
  ⟨bitVecSub left.bits right.bits⟩

/-- Signed addition (wraps `mod 2^n`; two's-complement identical to unsigned). -/
def SIntN.add {width : Nat} (left right : SIntN width) : SIntN width :=
  ⟨bitVecAdd left.bits right.bits⟩

/-- Signed multiplication. -/
def SIntN.mul {width : Nat} (left right : SIntN width) : SIntN width :=
  ⟨bitVecMul left.bits right.bits⟩

/-- Signed subtraction. -/
def SIntN.sub {width : Nat} (left right : SIntN width) : SIntN width :=
  ⟨bitVecSub left.bits right.bits⟩

/-- Signed negation (two's-complement complement). -/
def SIntN.neg {width : Nat} (value : SIntN width) : SIntN width :=
  ⟨bitVecNeg value.bits⟩

/-! ## The sign-sensitive ops (the ONLY place the u/i split shows) -/

/-- Unsigned right shift (logical, zero-fill). -/
def UIntN.shr {width : Nat} (value : UIntN width) (amount : Nat) : UIntN width :=
  ⟨bitVecShr value.bits amount⟩

/-- Signed right shift (arithmetic, sign-fill). -/
def SIntN.ashr {width : Nat} (value : SIntN width) (amount : Nat) : SIntN width :=
  ⟨bitVecAshr value.bits amount⟩

/-- Sign test on a signed view. -/
def SIntN.isNegative {width : Nat} (value : SIntN width) : Bool :=
  bitVecIsNegative value.bits

/-! ## Standard widths (FX §3.1)

The eight canonical unsigned and signed widths.  These 2-3 character names are
the SPEC-CANONICAL primitive type names of FX §3.1 (like `shift`/`subst` are
canonical kernel primitives), not ad-hoc abbreviations. -/

/-- 8-bit unsigned. -/
abbrev u8 := UIntN 8
/-- 16-bit unsigned. -/
abbrev u16 := UIntN 16
/-- 32-bit unsigned. -/
abbrev u32 := UIntN 32
/-- 64-bit unsigned. -/
abbrev u64 := UIntN 64
/-- 128-bit unsigned. -/
abbrev u128 := UIntN 128
/-- 256-bit unsigned. -/
abbrev u256 := UIntN 256
/-- 512-bit unsigned. -/
abbrev u512 := UIntN 512
/-- 1024-bit unsigned. -/
abbrev u1024 := UIntN 1024

/-- 8-bit signed. -/
abbrev i8 := SIntN 8
/-- 16-bit signed. -/
abbrev i16 := SIntN 16
/-- 32-bit signed. -/
abbrev i32 := SIntN 32
/-- 64-bit signed. -/
abbrev i64 := SIntN 64
/-- 128-bit signed. -/
abbrev i128 := SIntN 128
/-- 256-bit signed. -/
abbrev i256 := SIntN 256
/-- 512-bit signed. -/
abbrev i512 := SIntN 512
/-- 1024-bit signed. -/
abbrev i1024 := SIntN 1024

end FX1Poly.ComputerAlgebra
