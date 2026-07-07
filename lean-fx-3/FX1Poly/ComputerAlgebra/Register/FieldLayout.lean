import FX1Poly.ComputerAlgebra.Bits.BitVec

/-! # FieldLayout — register bit-field layout, extract/insert, and their round-trip

The register-level layer of the hardware substrate (fx_design.md §18.1 formats,
§18.4 cross-field dependencies).  A `Format` is a total bit-width; a `FieldSpec`
carves a `[offset, offset+width)` window out of it.  `extractField` reads a
window's contents; `insertField` splices a value INTO a window, leaving the bits
outside untouched.

The two central correctness facts:

* `extractField_insertField_same` — reading back a freshly-written field returns
  exactly what was written (given the field fits the register).
* `extractField_insertField_disjoint` — writing field `fs` leaves any DISJOINT
  field `other` bit-for-bit unchanged.

The design is the ARITHMETIC one (not the literal `and-not / or / shift`): every
op is a `bitVecOfNatMod` whose argument is a `natQuotient`/`natRemainder`/`* 2^k`
combination, so every proof rides the shipped propext-clean modular corpus
(`NatModularReduction`, `NatEuclideanDivision`) instead of the un-lemmatized
bitwise folds or the propext-dirty `<<<`/`>>>` div/mul bridge.  This is
bit-identical to the mask/shift phrasing but zero-axiom-provable now.

`Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The layout structures -/

/-- A register field: a `width`-bit window starting at bit `offset` (LSB-first). -/
structure FieldSpec where
  offset : Nat
  width  : Nat

/-- A register format: the total number of bits available. -/
structure Format where
  totalWidth : Nat

/-- `fs` fits inside `fmt`: its top bit is below the format's width. -/
def FieldSpec.fitsIn (fs : FieldSpec) (fmt : Format) : Prop :=
  fs.offset + fs.width ≤ fmt.totalWidth

/-- Two fields occupy disjoint bit ranges: either `other` sits entirely below
`fs`, or `fs` sits entirely below `other`. -/
def FieldSpec.isDisjointFrom (fs other : FieldSpec) : Prop :=
  other.offset + other.width ≤ fs.offset  ∨  fs.offset + fs.width ≤ other.offset

/-! ## Generic Nat helpers (clean mirrors of the propext-dirty Init lemmas) -/

/-- `2 ^ (a + b) = 2 ^ a * 2 ^ b` — Init's `Nat.pow_add` leaks propext; this rides
`Nat.pow_succ` + `natMulAssoc`.  Structural on the second exponent. -/
theorem twoPowAdd : ∀ (base exponentA exponentB : Nat),
    base ^ (exponentA + exponentB) = base ^ exponentA * base ^ exponentB
  | base, exponentA, 0 =>
      (congrArg (base ^ ·) (Nat.add_zero exponentA)).trans (Nat.mul_one (base ^ exponentA)).symm
  | base, exponentA, exponentB + 1 =>
      (congrArg (base ^ ·) (Nat.add_succ exponentA exponentB)).trans
        ((Nat.pow_succ base (exponentA + exponentB)).trans
          ((congrArg (· * base) (twoPowAdd base exponentA exponentB)).trans
            ((natMulAssoc (base ^ exponentA) (base ^ exponentB) base).trans
              (congrArg (base ^ exponentA * ·) (Nat.pow_succ base exponentB).symm))))

/-- Left-monotone multiplication — `Nat.mul_le_mul_left` without the propext. -/
theorem natMulLeMulLeft {small large : Nat} (factor : Nat) (isLe : small ≤ large) :
    factor * small ≤ factor * large :=
  match Nat.le.dest isLe with
  | ⟨witness, equation⟩ =>
      Nat.le.intro
        ((Nat.left_distrib factor small witness).symm.trans (congrArg (factor * ·) equation))

/-- Right-monotone multiplication — `Nat.mul_le_mul_right` without the propext. -/
theorem natMulLeMulRightBy (factor : Nat) {small large : Nat} (isLe : small ≤ large) :
    small * factor ≤ large * factor :=
  match Nat.le.dest isLe with
  | ⟨witness, equation⟩ =>
      Nat.le.intro
        ((natRightDistrib small witness factor).symm.trans (congrArg (· * factor) equation))

/-- Strict left-cancellation for multiplication: `factor * small < factor * large`
forces `small < large`.  The `witness = 0` case (`small = large`) contradicts the
strict hypothesis; the `witness+1` case delivers the strict bound. -/
theorem natLtOfMulLtMulLeft {small large factor : Nat}
    (isStrict : factor * small < factor * large) : small < large :=
  match natLeTotal large small with
  | .inl isLargeLeSmall =>
      (natSuccNeverLeSelf
        (Nat.lt_of_lt_of_le isStrict (natMulLeMulLeft factor isLargeLeSmall))).elim
  | .inr isSmallLeLarge =>
      match Nat.le.dest isSmallLeLarge with
      | ⟨0, equation⟩ =>
          let smallEqLarge : small = large := (Nat.add_zero small).symm.trans equation
          (natSuccNeverLeSelf
            (Nat.lt_of_lt_of_le isStrict
              (Nat.le_of_eq (congrArg (factor * ·) smallEqLarge).symm))).elim
      | ⟨witness + 1, equation⟩ =>
          Nat.le.intro ((Nat.add_right_comm small 1 witness).trans equation)

/-- `natQuotient` pinned by a bounded decomposition — the quotient sibling of
`natRemainderUnique`. -/
theorem natQuotientOfDecomp {dividend divisor quotient remainder : Nat}
    (isBounded : remainder < divisor)
    (decomposition : dividend = divisor * quotient + remainder) :
    natQuotient dividend divisor = quotient :=
  natEuclideanQuotientUnique
    (natRemainderIsBounded (Nat.lt_of_le_of_lt (Nat.zero_le remainder) isBounded))
    isBounded
    ((natRemainderReconstructs dividend divisor).symm.trans decomposition)

/-- If `dividend < divisor * bound` then the quotient is below `bound`.  The scaled
quotient `divisor * quotient` is at most `dividend` (drop the remainder), and
`dividend < divisor * bound`, so strict left-cancellation delivers `quotient <
bound`. -/
theorem natQuotientBound {dividend divisor bound : Nat}
    (isBelow : dividend < divisor * bound) : natQuotient dividend divisor < bound :=
  let scaledQuotientLeDividend : divisor * natQuotient dividend divisor ≤ dividend :=
    Nat.le.intro (natRemainderReconstructs dividend divisor).symm
  natLtOfMulLtMulLeft (Nat.lt_of_le_of_lt scaledQuotientLeDividend isBelow)

/-- The middle window `low + fieldValue * 2^offset` stays below `2^offset * 2^width`
when `low` and `fieldValue` are each below their bounds.  This is the "the written
window does not spill past the field's top bit" fact. -/
theorem natLowPlusScaledLt {low fieldValue lowModulus fieldModulus : Nat}
    (lowBound : low < lowModulus) (fieldBound : fieldValue < fieldModulus) :
    low + fieldValue * lowModulus < lowModulus * fieldModulus :=
  let scaledBound : fieldValue * lowModulus + lowModulus ≤ fieldModulus * lowModulus :=
    Nat.le_trans (Nat.le_of_eq (Nat.succ_mul fieldValue lowModulus).symm)
      (natMulLeMulRightBy lowModulus fieldBound)
  let scaledBoundReordered : fieldValue * lowModulus + lowModulus ≤ lowModulus * fieldModulus :=
    Nat.le_trans scaledBound (Nat.le_of_eq (Nat.mul_comm fieldModulus lowModulus))
  let underShift : low + fieldValue * lowModulus < fieldValue * lowModulus + lowModulus :=
    Nat.lt_of_le_of_lt (Nat.le_of_eq (Nat.add_comm low (fieldValue * lowModulus)))
      (Nat.add_lt_add_left lowBound (fieldValue * lowModulus))
  Nat.lt_of_lt_of_le underShift scaledBoundReordered

/-- The algebraic core of the write-then-read identity: the spliced natural
`low + fieldValue * P + high * (P * Q)` reveals `fieldValue + high * Q` as its
quotient by `P` (remainder `low`). -/
theorem natInsertDecomp (low fieldValue high lowModulus fieldModulus : Nat) :
    (low + fieldValue * lowModulus) + high * (lowModulus * fieldModulus)
      = lowModulus * (fieldValue + high * fieldModulus) + low :=
  let commutedField : fieldValue * lowModulus = lowModulus * fieldValue :=
    Nat.mul_comm fieldValue lowModulus
  let commutedHigh : high * (lowModulus * fieldModulus) = lowModulus * (high * fieldModulus) :=
    (Nat.mul_comm high (lowModulus * fieldModulus)).trans
      ((natMulAssoc lowModulus fieldModulus high).trans
        (congrArg (lowModulus * ·) (Nat.mul_comm fieldModulus high)))
  let lhsRewritten :
      (low + fieldValue * lowModulus) + high * (lowModulus * fieldModulus)
        = (low + lowModulus * fieldValue) + lowModulus * (high * fieldModulus) :=
    (congrArg (fun scaled => (low + scaled) + high * (lowModulus * fieldModulus)) commutedField).trans
      (congrArg (fun scaled => (low + lowModulus * fieldValue) + scaled) commutedHigh)
  let rearranged :
      (low + lowModulus * fieldValue) + lowModulus * (high * fieldModulus)
        = (lowModulus * fieldValue + lowModulus * (high * fieldModulus)) + low :=
    (congrArg (· + lowModulus * (high * fieldModulus))
        (Nat.add_comm low (lowModulus * fieldValue))).trans
      ((Nat.add_assoc (lowModulus * fieldValue) low (lowModulus * (high * fieldModulus))).trans
        ((congrArg (lowModulus * fieldValue + ·)
            (Nat.add_comm low (lowModulus * (high * fieldModulus)))).trans
          (Nat.add_assoc (lowModulus * fieldValue) (lowModulus * (high * fieldModulus)) low).symm))
  let rhsRewritten :
      (lowModulus * fieldValue + lowModulus * (high * fieldModulus)) + low
        = lowModulus * (fieldValue + high * fieldModulus) + low :=
    congrArg (· + low) (Nat.left_distrib lowModulus fieldValue (high * fieldModulus)).symm
  lhsRewritten.trans (rearranged.trans rhsRewritten)

/-- `natQuotient (addend + divisor * multiple) divisor = natQuotient addend divisor
+ multiple` — adding a multiple of the divisor bumps the quotient by that multiple
(remainder untouched).  The workhorse for the "field below the write is unchanged"
case. -/
theorem natQuotientAddMul {addend divisor multiple : Nat} (isPositive : 0 < divisor) :
    natQuotient (addend + divisor * multiple) divisor = natQuotient addend divisor + multiple :=
  let quotient := natQuotient addend divisor
  let remainder := natRemainder addend divisor
  let recon : addend = divisor * quotient + remainder := natRemainderReconstructs addend divisor
  let bound : remainder < divisor := natRemainderIsBounded isPositive
  let decomposition :
      addend + divisor * multiple = divisor * (quotient + multiple) + remainder :=
    (congrArg (· + divisor * multiple) recon).trans
      ((Nat.add_right_comm (divisor * quotient) remainder (divisor * multiple)).trans
        (congrArg (· + remainder) (Nat.left_distrib divisor quotient multiple).symm))
  natQuotientOfDecomp bound decomposition

/-- `natQuotient (low + high * blockModulus) (blockModulus * outerModulus) =
natQuotient high outerModulus` — dividing by a divisor that is a multiple of the
block size discards the low block entirely, independent of `low`.  The workhorse
for the "field above the write is unchanged" case. -/
theorem natQuotientHighCollapse {low high blockModulus outerModulus : Nat}
    (lowBound : low < blockModulus) (positiveOuter : 0 < outerModulus) :
    natQuotient (low + high * blockModulus) (blockModulus * outerModulus)
      = natQuotient high outerModulus :=
  let outerQuotient := natQuotient high outerModulus
  let outerRemainder := natRemainder high outerModulus
  let reconHigh : high = outerModulus * outerQuotient + outerRemainder :=
    natRemainderReconstructs high outerModulus
  let outerRemainderBound : outerRemainder < outerModulus := natRemainderIsBounded positiveOuter
  let blockAssoc :
      (outerModulus * outerQuotient) * blockModulus
        = (blockModulus * outerModulus) * outerQuotient :=
    (Nat.mul_comm (outerModulus * outerQuotient) blockModulus).trans
      (natMulAssoc blockModulus outerModulus outerQuotient).symm
  let decomposition :
      low + high * blockModulus
        = (blockModulus * outerModulus) * outerQuotient + (outerRemainder * blockModulus + low) :=
    (congrArg (fun expanded => low + expanded * blockModulus) reconHigh).trans
      ((congrArg (low + ·)
          (natRightDistrib (outerModulus * outerQuotient) outerRemainder blockModulus)).trans
        ((congrArg (fun scaled => low + (scaled + outerRemainder * blockModulus)) blockAssoc).trans
          ((Nat.add_comm low
              ((blockModulus * outerModulus) * outerQuotient + outerRemainder * blockModulus)).trans
            (Nat.add_assoc ((blockModulus * outerModulus) * outerQuotient)
              (outerRemainder * blockModulus) low))))
  let remainderBound :
      outerRemainder * blockModulus + low < blockModulus * outerModulus :=
    Nat.lt_of_le_of_lt
      (Nat.le_of_eq (Nat.add_comm (outerRemainder * blockModulus) low))
      (natLowPlusScaledLt lowBound outerRemainderBound)
  natQuotientOfDecomp remainderBound decomposition

/-- `addend + value ≤ target` gives `value ≤ target - addend` — Init's
`Nat.le_sub_of_add_le` leaks propext; this rides `Nat.le.dest` +
`natAddSubCancelLeft`. -/
theorem natLeSubOfAddLe {addend value target : Nat} (isLe : addend + value ≤ target) :
    value ≤ target - addend :=
  match Nat.le.dest isLe with
  | ⟨witness, equation⟩ =>
      let targetForm : target = addend + (value + witness) :=
        equation.symm.trans (Nat.add_assoc addend value witness)
      let subForm : target - addend = value + witness :=
        (congrArg (· - addend) targetForm).trans (natAddSubCancelLeft addend (value + witness))
      Nat.le_trans (Nat.le_add_right value witness) (Nat.le_of_eq subForm.symm)

/-! ## Field extract / insert (arithmetic form) -/

/-- Read the `fs.width`-bit window at `fs.offset`: shift `v` down by `offset`
(a quotient by `2^offset`), then keep the low `width` bits (`mod 2^width`). -/
def extractField {n : Nat} (v : BitVec n) (fs : FieldSpec) : BitVec fs.width :=
  bitVecOfNatMod (natQuotient v.toNat (2 ^ fs.offset))

/-- Splice `fieldValue` into the `fs` window of `v`: keep the bits below `offset`
(`v mod 2^offset`), overwrite the window with `fieldValue << offset`, and keep the
bits at/above `offset+width` (`(v >> (offset+width)) << (offset+width)`).  Stated
as a Euclidean split — no bitwise fold, no shift bridge. -/
def insertField {n : Nat} (v : BitVec n) (fs : FieldSpec) (fieldValue : BitVec fs.width) :
    BitVec n :=
  bitVecOfNatMod
    ( natRemainder v.toNat (2 ^ fs.offset)
    + fieldValue.toNat * 2 ^ fs.offset
    + natQuotient v.toNat (2 ^ (fs.offset + fs.width)) * 2 ^ (fs.offset + fs.width) )

/-! ## The splice does not overflow the register

The load-bearing bridge for BOTH round-trips: when `fs` fits, the spliced natural
`low + fieldValue*2^offset + high*2^(offset+width)` is already below `2^n`, so the
outer `mod 2^n` in `insertField` is the identity and `.toNat` reads the raw sum. -/

/-- `(insertField v fs fieldValue).toNat` is exactly the un-reduced splice sum. -/
theorem insertFieldToNat {n : Nat} (v : BitVec n) (fs : FieldSpec)
    (fieldValue : BitVec fs.width) (fits : fs.fitsIn ⟨n⟩) :
    (insertField v fs fieldValue).toNat
      = natRemainder v.toNat (2 ^ fs.offset)
        + fieldValue.toNat * 2 ^ fs.offset
        + natQuotient v.toNat (2 ^ (fs.offset + fs.width)) * 2 ^ (fs.offset + fs.width) :=
  let lowModulus := 2 ^ fs.offset
  let fieldModulus := 2 ^ fs.width
  let windowModulus := 2 ^ (fs.offset + fs.width)
  let low := natRemainder v.toNat lowModulus
  let fieldNat := fieldValue.toNat
  let high := natQuotient v.toNat windowModulus
  let insertArg := low + fieldNat * lowModulus + high * windowModulus
  let positiveLow : 0 < lowModulus := Nat.two_pow_pos fs.offset
  let lowBound : low < lowModulus := natRemainderIsBounded positiveLow
  let fieldBound : fieldNat < fieldModulus := fieldValue.isLt
  let windowFactored : windowModulus = lowModulus * fieldModulus := twoPowAdd 2 fs.offset fs.width
  let middleBelowWindow : low + fieldNat * lowModulus < windowModulus :=
    Nat.lt_of_lt_of_le (natLowPlusScaledLt lowBound fieldBound)
      (Nat.le_of_eq windowFactored.symm)
  let registerFactored : (2 : Nat) ^ n = windowModulus * 2 ^ (n - (fs.offset + fs.width)) :=
    (congrArg (2 ^ ·) (natAddSubOfLe fits).symm).trans
      (twoPowAdd 2 (fs.offset + fs.width) (n - (fs.offset + fs.width)))
  let highBound : high < 2 ^ (n - (fs.offset + fs.width)) :=
    natQuotientBound (Nat.lt_of_lt_of_le v.isLt (Nat.le_of_eq registerFactored))
  let spliceBelowRegister : insertArg < 2 ^ n :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_right middleBelowWindow (high * windowModulus))
      (Nat.le_trans
        (Nat.le_of_eq
          ((Nat.add_comm windowModulus (high * windowModulus)).trans
            (Nat.succ_mul high windowModulus).symm))
        (Nat.le_trans (natMulLeMulRightBy windowModulus highBound)
          (Nat.le_of_eq
            ((Nat.mul_comm (2 ^ (n - (fs.offset + fs.width))) windowModulus).trans
              registerFactored.symm))))
  (bitVecOfNatModToNat insertArg).trans (natRemainderOfLt spliceBelowRegister)

/-! ## Round-trip 1: read-back of a freshly-written field -/

/-- Reading the field just written returns exactly the written value, provided the
field fits inside the register. -/
theorem extractField_insertField_same {n : Nat} (v : BitVec n) (fs : FieldSpec)
    (fieldValue : BitVec fs.width) (fits : fs.fitsIn ⟨n⟩) :
    extractField (insertField v fs fieldValue) fs = fieldValue :=
  let lowModulus := 2 ^ fs.offset
  let fieldModulus := 2 ^ fs.width
  let windowModulus := 2 ^ (fs.offset + fs.width)
  let low := natRemainder v.toNat lowModulus
  let fieldNat := fieldValue.toNat
  let high := natQuotient v.toNat windowModulus
  let insertArg := low + fieldNat * lowModulus + high * windowModulus
  let positiveLow : 0 < lowModulus := Nat.two_pow_pos fs.offset
  let lowBound : low < lowModulus := natRemainderIsBounded positiveLow
  let fieldBound : fieldNat < fieldModulus := fieldValue.isLt
  let windowFactored : windowModulus = lowModulus * fieldModulus := twoPowAdd 2 fs.offset fs.width
  let insertToNat : (insertField v fs fieldValue).toNat = insertArg :=
    insertFieldToNat v fs fieldValue fits
  let spliceDecomposition :
      insertArg = lowModulus * (fieldNat + high * fieldModulus) + low :=
    (congrArg (fun window => low + fieldNat * lowModulus + high * window) windowFactored).trans
      (natInsertDecomp low fieldNat high lowModulus fieldModulus)
  let quotientEq : natQuotient insertArg lowModulus = fieldNat + high * fieldModulus :=
    natQuotientOfDecomp lowBound spliceDecomposition
  let remainderDecomposition :
      fieldNat + high * fieldModulus = fieldModulus * high + fieldNat :=
    (Nat.add_comm fieldNat (high * fieldModulus)).trans
      (congrArg (· + fieldNat) (Nat.mul_comm high fieldModulus))
  let remainderEq : natRemainder (fieldNat + high * fieldModulus) fieldModulus = fieldNat :=
    natRemainderUnique fieldBound remainderDecomposition
  let toNatEq : (extractField (insertField v fs fieldValue) fs).toNat = fieldValue.toNat :=
    (bitVecOfNatModToNat (natQuotient (insertField v fs fieldValue).toNat lowModulus)).trans
      ((congrArg (fun spliced => natRemainder (natQuotient spliced lowModulus) fieldModulus)
          insertToNat).trans
        ((congrArg (fun quotient => natRemainder quotient fieldModulus) quotientEq).trans
          remainderEq))
  BitVec.eq_of_toNat_eq toNatEq

/-! ## Round-trip 2: a write leaves a disjoint field untouched -/

/-- Writing field `fs` leaves any DISJOINT field `other` bit-for-bit unchanged.
Two symmetric cases: `other` sits entirely above the write window (the write's low
bits are discarded by the larger quotient — `natQuotientHighCollapse`), or `other`
sits entirely below it (the write only touches high bits, a multiple of `other`'s
modulus — `natQuotientAddMul` + `natRemainderAddMultiple`). -/
theorem extractField_insertField_disjoint {n : Nat} (v : BitVec n)
    (fs other : FieldSpec) (fieldValue : BitVec fs.width)
    (fits : fs.fitsIn ⟨n⟩) (disjoint : fs.isDisjointFrom other) :
    extractField (insertField v fs fieldValue) other = extractField v other :=
  let lowModulus := 2 ^ fs.offset
  let fieldModulus := 2 ^ fs.width
  let windowModulus := 2 ^ (fs.offset + fs.width)
  let otherModulus := 2 ^ other.offset
  let otherFieldModulus := 2 ^ other.width
  let low := natRemainder v.toNat lowModulus
  let fieldNat := fieldValue.toNat
  let high := natQuotient v.toNat windowModulus
  let insertArg := low + fieldNat * lowModulus + high * windowModulus
  let positiveLow : 0 < lowModulus := Nat.two_pow_pos fs.offset
  let positiveWindow : 0 < windowModulus := Nat.two_pow_pos (fs.offset + fs.width)
  let positiveOther : 0 < otherModulus := Nat.two_pow_pos other.offset
  let positiveOtherField : 0 < otherFieldModulus := Nat.two_pow_pos other.width
  let lowBound : low < lowModulus := natRemainderIsBounded positiveLow
  let fieldBound : fieldNat < fieldModulus := fieldValue.isLt
  let insertToNat : (insertField v fs fieldValue).toNat = insertArg :=
    insertFieldToNat v fs fieldValue fits
  let bodyEq :
      natRemainder (natQuotient insertArg otherModulus) otherFieldModulus
        = natRemainder (natQuotient v.toNat otherModulus) otherFieldModulus :=
    match disjoint with
    | .inr aboveWrite =>
        let blockQuotientModulus := 2 ^ (other.offset - (fs.offset + fs.width))
        let positiveBlockQuotient : 0 < blockQuotientModulus :=
          Nat.two_pow_pos (other.offset - (fs.offset + fs.width))
        let otherFactored : otherModulus = windowModulus * blockQuotientModulus :=
          (congrArg (2 ^ ·) (natAddSubOfLe aboveWrite).symm).trans
            (twoPowAdd 2 (fs.offset + fs.width) (other.offset - (fs.offset + fs.width)))
        let windowFactored : windowModulus = lowModulus * fieldModulus := twoPowAdd 2 fs.offset fs.width
        let middleBelowWindow : low + fieldNat * lowModulus < windowModulus :=
          Nat.lt_of_lt_of_le (natLowPlusScaledLt lowBound fieldBound)
            (Nat.le_of_eq windowFactored.symm)
        let quotientInsert :
            natQuotient insertArg otherModulus = natQuotient high blockQuotientModulus :=
          (congrArg (natQuotient insertArg ·) otherFactored).trans
            (natQuotientHighCollapse middleBelowWindow positiveBlockQuotient)
        let lowRemainder := natRemainder v.toNat windowModulus
        let lowRemainderBound : lowRemainder < windowModulus := natRemainderIsBounded positiveWindow
        let valueReconstructed : v.toNat = lowRemainder + high * windowModulus :=
          (natRemainderReconstructs v.toNat windowModulus).trans
            ((Nat.add_comm (windowModulus * high) lowRemainder).trans
              (congrArg (lowRemainder + ·) (Nat.mul_comm windowModulus high)))
        let quotientValue :
            natQuotient v.toNat otherModulus = natQuotient high blockQuotientModulus :=
          (congrArg (natQuotient v.toNat ·) otherFactored).trans
            ((congrArg (natQuotient · (windowModulus * blockQuotientModulus)) valueReconstructed).trans
              (natQuotientHighCollapse lowRemainderBound positiveBlockQuotient))
        (congrArg (fun quotient => natRemainder quotient otherFieldModulus) quotientInsert).trans
          (congrArg (fun quotient => natRemainder quotient otherFieldModulus) quotientValue).symm
    | .inl belowWrite =>
        let offsetGap := 2 ^ (fs.offset - other.offset)
        let otherAtMostOffset : other.offset ≤ fs.offset :=
          Nat.le_trans (Nat.le_add_right other.offset other.width) belowWrite
        let lowFactored : lowModulus = otherModulus * offsetGap :=
          (congrArg (2 ^ ·) (natAddSubOfLe otherAtMostOffset).symm).trans
            (twoPowAdd 2 other.offset (fs.offset - other.offset))
        let widthWithinGap : other.width ≤ fs.offset - other.offset := natLeSubOfAddLe belowWrite
        let residualGap := 2 ^ ((fs.offset - other.offset) - other.width)
        let gapFactored : offsetGap = otherFieldModulus * residualGap :=
          (congrArg (2 ^ ·) (natAddSubOfLe widthWithinGap).symm).trans
            (twoPowAdd 2 other.width ((fs.offset - other.offset) - other.width))
        let windowSplitsLow : windowModulus = lowModulus * fieldModulus := twoPowAdd 2 fs.offset fs.width
        let innerScaled := fieldNat + high * fieldModulus
        let commutedHigh : high * (lowModulus * fieldModulus) = lowModulus * (high * fieldModulus) :=
          (Nat.mul_comm high (lowModulus * fieldModulus)).trans
            ((natMulAssoc lowModulus fieldModulus high).trans
              (congrArg (lowModulus * ·) (Nat.mul_comm fieldModulus high)))
        let scaledSum : fieldNat * lowModulus + high * windowModulus = lowModulus * innerScaled :=
          (congrArg (fun window => fieldNat * lowModulus + high * window) windowSplitsLow).trans
            ((congrArg (fieldNat * lowModulus + ·) commutedHigh).trans
              ((congrArg (· + lowModulus * (high * fieldModulus)) (Nat.mul_comm fieldNat lowModulus)).trans
                (Nat.left_distrib lowModulus fieldNat (high * fieldModulus)).symm))
        let insertGrouped : insertArg = low + lowModulus * innerScaled :=
          (Nat.add_assoc low (fieldNat * lowModulus) (high * windowModulus)).trans
            (congrArg (low + ·) scaledSum)
        let insertViaOther : insertArg = low + otherModulus * (offsetGap * innerScaled) :=
          insertGrouped.trans
            (congrArg (low + ·)
              ((congrArg (· * innerScaled) lowFactored).trans
                (natMulAssoc otherModulus offsetGap innerScaled)))
        let quotientInsert :
            natQuotient insertArg otherModulus
              = natQuotient low otherModulus + offsetGap * innerScaled :=
          (congrArg (natQuotient · otherModulus) insertViaOther).trans
            (natQuotientAddMul positiveOther)
        let gapMultipleInsert :
            offsetGap * innerScaled = otherFieldModulus * (residualGap * innerScaled) :=
          (congrArg (· * innerScaled) gapFactored).trans
            (natMulAssoc otherFieldModulus residualGap innerScaled)
        let remainderInsert :
            natRemainder (natQuotient insertArg otherModulus) otherFieldModulus
              = natRemainder (natQuotient low otherModulus) otherFieldModulus :=
          (congrArg (fun quotient => natRemainder quotient otherFieldModulus) quotientInsert).trans
            ((congrArg
                (fun scaled =>
                  natRemainder (natQuotient low otherModulus + scaled) otherFieldModulus)
                gapMultipleInsert).trans
              (natRemainderAddMultiple (natQuotient low otherModulus) otherFieldModulus
                (residualGap * innerScaled) positiveOtherField))
        let valueQuotient := natQuotient v.toNat lowModulus
        let valueGrouped : v.toNat = low + lowModulus * valueQuotient :=
          (natRemainderReconstructs v.toNat lowModulus).trans
            (Nat.add_comm (lowModulus * valueQuotient) low)
        let valueViaOther : v.toNat = low + otherModulus * (offsetGap * valueQuotient) :=
          valueGrouped.trans
            (congrArg (low + ·)
              ((congrArg (· * valueQuotient) lowFactored).trans
                (natMulAssoc otherModulus offsetGap valueQuotient)))
        let quotientValue :
            natQuotient v.toNat otherModulus
              = natQuotient low otherModulus + offsetGap * valueQuotient :=
          (congrArg (natQuotient · otherModulus) valueViaOther).trans
            (natQuotientAddMul positiveOther)
        let gapMultipleValue :
            offsetGap * valueQuotient = otherFieldModulus * (residualGap * valueQuotient) :=
          (congrArg (· * valueQuotient) gapFactored).trans
            (natMulAssoc otherFieldModulus residualGap valueQuotient)
        let remainderValue :
            natRemainder (natQuotient v.toNat otherModulus) otherFieldModulus
              = natRemainder (natQuotient low otherModulus) otherFieldModulus :=
          (congrArg (fun quotient => natRemainder quotient otherFieldModulus) quotientValue).trans
            ((congrArg
                (fun scaled =>
                  natRemainder (natQuotient low otherModulus + scaled) otherFieldModulus)
                gapMultipleValue).trans
              (natRemainderAddMultiple (natQuotient low otherModulus) otherFieldModulus
                (residualGap * valueQuotient) positiveOtherField))
        remainderInsert.trans remainderValue.symm
  let toNatEq :
      (extractField (insertField v fs fieldValue) other).toNat = (extractField v other).toNat :=
    (bitVecOfNatModToNat (natQuotient (insertField v fs fieldValue).toNat otherModulus)).trans
      ((congrArg
          (fun spliced =>
            natRemainder (natQuotient spliced otherModulus) otherFieldModulus) insertToNat).trans
        (bodyEq.trans
          (bitVecOfNatModToNat (natQuotient v.toNat otherModulus)).symm))
  BitVec.eq_of_toNat_eq toNatEq

end FX1Poly.ComputerAlgebra
