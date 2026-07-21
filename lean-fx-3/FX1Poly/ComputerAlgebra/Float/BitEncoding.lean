import FX1Poly.ComputerAlgebra.Register.FieldLayout
import FX1Poly.ComputerAlgebra.Float.FloatFormat

/-! # BitEncoding — sign|exponent|mantissa bit packing with a decode/encode round-trip

The physical-interchange codec for the IEEE / ML low-precision formats
(fx_design.md §18.1 bit formats).  A `BitLayout` is a `(expWidth, mantWidth)`
pair; a value packs into a `BitVec (1 + expWidth + mantWidth)` as three
LSB-first fields — mantissa at offset `0`, exponent at offset `mantWidth`, sign
at offset `mantWidth + expWidth`.

Everything rides the `Register/FieldLayout` codec (`insertField` /
`extractField`) and its two proven round-trips (`extractField_insertField_same`,
`extractField_insertField_disjoint`).  The round-trip theorem is
`decodeEncode_*`: decoding each of the three fields out of a freshly-encoded
word returns exactly the field that was written.  Instantiated for
binary16/32/64, FP8 E4M3/E5M2, FP4 E2M1 with their exact widths.

`Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The layout -/

/-- A float bit layout: `expWidth` exponent bits and `mantWidth` trailing-mantissa
bits, plus one sign bit.  Total width is `1 + expWidth + mantWidth`. -/
structure BitLayout where
  expWidth  : Nat
  mantWidth : Nat

namespace BitLayout

/-- Total encoded width: trailing mantissa + exponent + sign, in mantissa-first
order (physical `1 + e + m` bits), so the field bounds follow from
`Nat.le_add_right` / `Nat.le_succ` with no reassociation. -/
def totalWidth (layout : BitLayout) : Nat := layout.mantWidth + layout.expWidth + 1

/-- The mantissa field: `mantWidth` bits at offset `0`. -/
def mantSpec (layout : BitLayout) : FieldSpec := { offset := 0, width := layout.mantWidth }

/-- The exponent field: `expWidth` bits at offset `mantWidth`. -/
def expSpec (layout : BitLayout) : FieldSpec :=
  { offset := layout.mantWidth, width := layout.expWidth }

/-- The sign field: one bit at offset `mantWidth + expWidth`. -/
def signSpec (layout : BitLayout) : FieldSpec :=
  { offset := layout.mantWidth + layout.expWidth, width := 1 }

/-! ## The concrete format layouts (widths from IEEE-754 / OCP OFP8 / OCP MX) -/

/-- binary16: 5 exponent bits, 10 trailing mantissa bits (16 total). -/
def binary16 : BitLayout := { expWidth := 5, mantWidth := 10 }

/-- binary32: 8 exponent bits, 23 trailing mantissa bits (32 total). -/
def binary32 : BitLayout := { expWidth := 8, mantWidth := 23 }

/-- binary64: 11 exponent bits, 52 trailing mantissa bits (64 total). -/
def binary64 : BitLayout := { expWidth := 11, mantWidth := 52 }

/-- FP8 E4M3: 4 exponent bits, 3 trailing mantissa bits (8 total). -/
def fp8E4M3 : BitLayout := { expWidth := 4, mantWidth := 3 }

/-- FP8 E5M2: 5 exponent bits, 2 trailing mantissa bits (8 total). -/
def fp8E5M2 : BitLayout := { expWidth := 5, mantWidth := 2 }

/-- FP4 E2M1: 2 exponent bits, 1 trailing mantissa bit (4 total). -/
def fp4E2M1 : BitLayout := { expWidth := 2, mantWidth := 1 }

end BitLayout

/-! ## The Nat side-conditions: every field fits, and the fields are pairwise disjoint

All are simple `≤` facts on `1 + expWidth + mantWidth`; proved with the
`Nat.le_add_*` primitives (no `omega`). -/

/-- The mantissa field fits inside the word: `0 + mantWidth ≤ mantWidth + expWidth + 1`. -/
theorem mantSpecFits (layout : BitLayout) :
    layout.mantSpec.fitsIn ⟨layout.totalWidth⟩ :=
  Nat.le_trans (Nat.le_of_eq (Nat.zero_add layout.mantWidth))
    (Nat.le_trans (Nat.le_add_right layout.mantWidth layout.expWidth)
      (Nat.le_succ (layout.mantWidth + layout.expWidth)))

/-- The exponent field fits inside the word: `mantWidth + expWidth ≤ mantWidth +
expWidth + 1`. -/
theorem expSpecFits (layout : BitLayout) :
    layout.expSpec.fitsIn ⟨layout.totalWidth⟩ :=
  Nat.le_succ (layout.mantWidth + layout.expWidth)

/-- The sign field fits inside the word (top bit): `(mantWidth + expWidth) + 1 ≤
mantWidth + expWidth + 1`. -/
theorem signSpecFits (layout : BitLayout) :
    layout.signSpec.fitsIn ⟨layout.totalWidth⟩ :=
  Nat.le_refl (layout.mantWidth + layout.expWidth + 1)

/-- The sign field is disjoint from the mantissa field:
`0 + mantWidth ≤ mantWidth + expWidth`. -/
theorem signDisjointMant (layout : BitLayout) :
    layout.signSpec.isDisjointFrom layout.mantSpec :=
  Or.inl (Nat.le_trans (Nat.le_of_eq (Nat.zero_add layout.mantWidth))
    (Nat.le_add_right layout.mantWidth layout.expWidth))

/-- The sign field is disjoint from the exponent field:
`mantWidth + expWidth ≤ mantWidth + expWidth`. -/
theorem signDisjointExp (layout : BitLayout) :
    layout.signSpec.isDisjointFrom layout.expSpec :=
  Or.inl (Nat.le_refl (layout.mantWidth + layout.expWidth))

/-- The exponent field is disjoint from the mantissa field:
`0 + mantWidth ≤ mantWidth`. -/
theorem expDisjointMant (layout : BitLayout) :
    layout.expSpec.isDisjointFrom layout.mantSpec :=
  Or.inl (Nat.le_of_eq (Nat.zero_add layout.mantWidth))

/-! ## Encode / decode -/

/-- Pack `(sign, exponent, mantissa)` fields into one word: splice each into a
zeroed register. -/
def encodeFields (layout : BitLayout)
    (signBit : BitVec 1) (exponentBits : BitVec layout.expWidth)
    (mantissaBits : BitVec layout.mantWidth) : BitVec layout.totalWidth :=
  insertField
    (insertField
      (insertField (bitVecZero (width := layout.totalWidth)) layout.mantSpec mantissaBits)
      layout.expSpec exponentBits)
    layout.signSpec signBit

/-- Read the sign field out of a word. -/
def decodeSign (layout : BitLayout) (word : BitVec layout.totalWidth) : BitVec 1 :=
  extractField word layout.signSpec

/-- Read the exponent field out of a word. -/
def decodeExponent (layout : BitLayout) (word : BitVec layout.totalWidth) :
    BitVec layout.expWidth :=
  extractField word layout.expSpec

/-- Read the mantissa field out of a word. -/
def decodeMantissa (layout : BitLayout) (word : BitVec layout.totalWidth) :
    BitVec layout.mantWidth :=
  extractField word layout.mantSpec

/-! ## The round-trip: decode of encode returns each written field

The sign field is the outermost write, so its read-back is one
`extractField_insertField_same`.  The exponent and mantissa reads must first
peel the disjoint outer write(s) via `extractField_insertField_disjoint`. -/

/-- Decoding the sign of an encoded word returns the sign that was written. -/
theorem decodeEncodeSign (layout : BitLayout)
    (signBit : BitVec 1) (exponentBits : BitVec layout.expWidth)
    (mantissaBits : BitVec layout.mantWidth) :
    decodeSign layout (encodeFields layout signBit exponentBits mantissaBits) = signBit :=
  extractField_insertField_same
    (insertField
      (insertField (bitVecZero (width := layout.totalWidth)) layout.mantSpec mantissaBits)
      layout.expSpec exponentBits)
    layout.signSpec signBit (signSpecFits layout)

/-- Decoding the exponent of an encoded word returns the exponent that was written.
Peel the disjoint sign write, then read back the freshly-written exponent. -/
theorem decodeEncodeExponent (layout : BitLayout)
    (signBit : BitVec 1) (exponentBits : BitVec layout.expWidth)
    (mantissaBits : BitVec layout.mantWidth) :
    decodeExponent layout (encodeFields layout signBit exponentBits mantissaBits) = exponentBits :=
  let afterMant :=
    insertField (bitVecZero (width := layout.totalWidth)) layout.mantSpec mantissaBits
  let afterExp := insertField afterMant layout.expSpec exponentBits
  (extractField_insertField_disjoint afterExp layout.signSpec layout.expSpec signBit
      (signSpecFits layout) (signDisjointExp layout)).trans
    (extractField_insertField_same afterMant layout.expSpec exponentBits (expSpecFits layout))

/-- Decoding the mantissa of an encoded word returns the mantissa that was written.
Peel the two disjoint outer writes (sign, exponent), then read back the mantissa. -/
theorem decodeEncodeMantissa (layout : BitLayout)
    (signBit : BitVec 1) (exponentBits : BitVec layout.expWidth)
    (mantissaBits : BitVec layout.mantWidth) :
    decodeMantissa layout (encodeFields layout signBit exponentBits mantissaBits) = mantissaBits :=
  let afterMant :=
    insertField (bitVecZero (width := layout.totalWidth)) layout.mantSpec mantissaBits
  let afterExp := insertField afterMant layout.expSpec exponentBits
  (extractField_insertField_disjoint afterExp layout.signSpec layout.mantSpec signBit
      (signSpecFits layout) (signDisjointMant layout)).trans
    ((extractField_insertField_disjoint afterMant layout.expSpec layout.mantSpec exponentBits
        (expSpecFits layout) (expDisjointMant layout)).trans
      (extractField_insertField_same (bitVecZero (width := layout.totalWidth)) layout.mantSpec
        mantissaBits (mantSpecFits layout)))

end FX1Poly.ComputerAlgebra
