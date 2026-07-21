import FX1Poly.ComputerAlgebra.FixedWidth.OverflowArithmetic
import FX1Poly.ComputerAlgebra.FixedWidth.Widening
import FX1Poly.ComputerAlgebra.Decision.BitVectorArithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # FixedWidth/SignedSemantics — the signed half of dimension 16 (trap, saturate, extend)

The unsigned overflow corpus (`OverflowArithmetic`, `SaturateMulSemantics`,
`Widening`) certifies wrap, trap, saturate, and zero-extension on the `[0, 2^n)`
reading.  This file supplies the signed half over the same substrate: the
two's-complement window `[-2^(n-1), 2^(n-1))` read through the encoding
`SIntN.signedValue = bitVecToInt bits`, where the sign test is the structural
`bitVecIsNegative = !decide (2 * toNat < 2^n)` (spec §3.1, §3.8).

## The subtraction-free convention

Every statement is phrased in the encoding's own `Nat` terms rather than through
library `Int` lemmas (the two `sIntNSignedValueOf*` anchors mention `Int` in
their statement only; their proofs are single `congrArg`s over the sign flag).
The window bookkeeping runs through one interpretation helper:

* `sIntNBiasedValue value = signedValue value + 2^(n-1)`, a `Nat` in
  `[0, 2^n)` — top bit clear: `toNat + 2^(n-1)`; top bit set: the complement
  magnitude `toNat - 2^(n-1)`, characterized additively
  (`sIntNBiasedValueOfNegative : biased + 2^(n-1) = toNat`).

In biased coordinates the signed window is `[0, 2^n)`, the exact signed sum of
two operands is `biased left + biased right` shifted by one modulus, and the
exact signed product is `sIntNMulBiasedShiftedProduct - sIntNMulBiasCross`
(`s1*s2 = (b1*b2 + 2^(n-1)*2^(n-1)) - (2^(n-1)*b1 + 2^(n-1)*b2)`), so every
fits test and every exactness equation is a pure `Nat` (in)equality.

## Signed range, trap, saturation, sign extension, and the BitVec value bridge

1. Signed range — `sIntNValueIsBounded` (the `Views` promise): top bit
   clear ⟹ `toNat < 2^(n-1)` (so `signedValue = toNat < 2^(n-1)`); top bit
   set ⟹ `2^(n-1) ≤ toNat` (so `signedValue = toNat - 2^n ≥ -2^(n-1)`).
2. Signed trap — `sIntNTrapAdd` / `sIntNTrapMul` return `some` exactly on the
   signed window, `none` on signed overflow (both sides), and the `some`
   payload's biased value satisfies the exact sum/product `Nat` equation
   (`sIntNTrapAddSomeIsExact`, `sIntNTrapMulSomeIsExact`).
3. Signed saturation — `sIntNSaturateAdd` / `sIntNSaturateMul` clamp to
   `sIntNMostNegative` (`toNat = 2^(n-1)`, i.e. `-2^(n-1)`) below and
   `sIntNMostPositive` (`toNat + 1 = 2^(n-1)`, i.e. `2^(n-1) - 1`) above, and
   are exact in range.
4. Sign extension — `SIntN.signExtend` preserves the signed value: top bit
   clear reduces to the zero-extension reading (`toNat` unchanged); top bit set
   preserves the complement magnitude additively
   (`extToNat + 2^width = toNat + 2^(width+extra)`); the sign bit is preserved.
5. BitVec value bridge — `fwsBitVecToBvaBits` converts a `BitVec` to the
   `Decision/BitVectorArithmetic` little-endian `List Bool` carrier, and
   `fwsBitVecToBvaBitsToNat` / `fwsBitVecToBvaBitsRoundTrip` identify its
   Horner reading `bvaToNat` with `BitVec.toNat`.

Everything windowed is indexed by `width + 1` (positive width) so the half
modulus `2^width` is meaningful.

`Init`-only, structural, genuine-`Eq`, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## `Bool` flag plumbing (full enumeration, no wildcards) -/

/-- A negated flag equal to `false` pins the flag `true`. -/
theorem fwsFlagEqTrueOfNotEqFalse : ∀ {flag : Bool}, (!flag) = false → flag = true
  | true, _negatedEqFalse => rfl
  | false, notEqFalse => Bool.noConfusion notEqFalse

/-- A negated flag equal to `true` pins the flag `false`. -/
theorem fwsFlagEqFalseOfNotEqTrue : ∀ {flag : Bool}, (!flag) = true → flag = false
  | false, _negatedEqTrue => rfl
  | true, notEqTrue => Bool.noConfusion notEqTrue

/-- Every flag is `true` or `false` (the decidable dichotomy, hand-rolled). -/
theorem fwsFlagIsTrueOrFalse : ∀ flag : Bool, flag = true ∨ flag = false
  | true => Or.inl rfl
  | false => Or.inr rfl

/-! ## The sign bit as a structural order fact

`bitVecIsNegative value = !decide (2 * toNat < 2^n)`, so the sign flag converts
to and from the doubled strict comparison by `decide` plumbing alone. -/

/-- The sign bit is clear when the doubled value stays below the modulus. -/
theorem fwsBitVecIsNegativeEqFalseOfDoubleLt {width : Nat} {value : BitVec width}
    (isBelowHalfDoubled : 2 * value.toNat < 2 ^ width) :
    bitVecIsNegative value = false :=
  congrArg Bool.not (decide_eq_true isBelowHalfDoubled)

/-- The sign bit is set when the doubled value reaches the modulus. -/
theorem fwsBitVecIsNegativeEqTrueOfDoubleGe {width : Nat} {value : BitVec width}
    (isAboveHalfDoubled : 2 ^ width ≤ 2 * value.toNat) :
    bitVecIsNegative value = true :=
  congrArg Bool.not
    (decide_eq_false (fun isBelow =>
      Nat.lt_irrefl (2 ^ width) (Nat.lt_of_le_of_lt isAboveHalfDoubled isBelow)))

/-- A clear sign bit yields the doubled strict bound. -/
theorem fwsDoubleLtOfBitVecNonNegative {width : Nat} {value : BitVec width}
    (isNonNegative : bitVecIsNegative value = false) :
    2 * value.toNat < 2 ^ width :=
  of_decide_eq_true (fwsFlagEqTrueOfNotEqFalse isNonNegative)

/-- A set sign bit yields the doubled lower bound. -/
theorem fwsDoubleGeOfBitVecNegative {width : Nat} {value : BitVec width}
    (isNegative : bitVecIsNegative value = true) :
    2 ^ width ≤ 2 * value.toNat :=
  match Nat.lt_or_ge (2 * value.toNat) (2 ^ width) with
  | .inl isBelow =>
      (of_decide_eq_false (fwsFlagEqFalseOfNotEqTrue isNegative) isBelow).elim
  | .inr isAbove => isAbove

/-! ## Doubling and halving the `Nat` order (structural, no cancellation imports) -/

/-- Doubling is monotone (structural induction on the `≤` witness). -/
theorem fwsDoubleLeDoubleOfLe {small large : Nat} (isLe : small ≤ large) :
    2 * small ≤ 2 * large := by
  induction isLe with
  | refl => exact Nat.le_refl (2 * small)
  | step _previousLe doubledLe => exact Nat.le_trans doubledLe (Nat.le_add_right _ 2)

/-- Doubling is strictly monotone. -/
theorem fwsDoubleLtDoubleOfLt {small large : Nat} (isLt : small < large) :
    2 * small < 2 * large :=
  Nat.lt_of_lt_of_le (Nat.succ_le_succ (Nat.le_succ (2 * small)))
    (fwsDoubleLeDoubleOfLe isLt)

/-- Halving a doubled `≤` (trichotomy; the reversed case doubles back to a
contradiction). -/
theorem fwsLeOfDoubleLeDouble {small large : Nat}
    (isDoubledLe : 2 * small ≤ 2 * large) : small ≤ large :=
  match Nat.lt_or_ge large small with
  | .inl isReversed =>
      (Nat.lt_irrefl (2 * large)
        (Nat.lt_of_lt_of_le (fwsDoubleLtDoubleOfLt isReversed) isDoubledLe)).elim
  | .inr isLe => isLe

/-- Halving a doubled `<`. -/
theorem fwsLtOfDoubleLtDouble {small large : Nat}
    (isDoubledLt : 2 * small < 2 * large) : small < large :=
  match Nat.lt_or_ge small large with
  | .inl isLt => isLt
  | .inr isGe =>
      (Nat.lt_irrefl (2 * small)
        (Nat.lt_of_lt_of_le isDoubledLt (fwsDoubleLeDoubleOfLe isGe))).elim

/-- Left-addend cancellation for `≤`, avoiding Init's `Nat.le_of_add_le_add_left`
(which routes through `propext`). -/
theorem fwsLeOfAddLeAddLeft {sharedAddend lowValue highValue : Nat}
    (isLe : sharedAddend + lowValue ≤ sharedAddend + highValue) :
    lowValue ≤ highValue :=
  match Nat.lt_or_ge highValue lowValue with
  | .inl isReversed =>
      (Nat.lt_irrefl (sharedAddend + highValue)
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_left isReversed sharedAddend) isLe)).elim
  | .inr isLe' => isLe'

/-! ## Half-modulus arithmetic -/

/-- `2 * 2^n = 2^(n+1)` (the successor power is definitional on the right). -/
theorem fwsDoublePow {width : Nat} : 2 * 2 ^ width = 2 ^ (width + 1) :=
  Nat.mul_comm 2 (2 ^ width)

/-- `2^n + 2^n = 2^(n+1)`, stated additively. -/
theorem fwsHalfAddHalf {width : Nat} : 2 ^ width + 2 ^ width = 2 ^ (width + 1) :=
  (congrArg (fun scaled => scaled + 2 ^ width) (Nat.mul_one (2 ^ width))).symm

/-- The half modulus is below the modulus. -/
theorem fwsHalfLtModulus {width : Nat} : 2 ^ width < 2 ^ (width + 1) :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.two_pow_pos width) (2 ^ width))
    (Nat.le_of_eq fwsHalfAddHalf)

/-- Widening never shrinks the modulus. -/
theorem fwsPowLeWiderPow {width extra : Nat} : 2 ^ width ≤ 2 ^ (width + extra) :=
  (twoPowAdd 2 width extra).symm ▸
    Nat.le_mul_of_pos_right (2 ^ width) (Nat.two_pow_pos extra)

/-! ## The signed range

`signedValue = toNat` when the top bit is clear and `toNat - 2^(n+1)` (as `Int`)
when set, so the window `[-2^n, 2^n)` at width `n+1` is exactly the pair of
`Nat` facts below, stated subtraction-free. -/

/-- Top bit clear ⟹ the raw reading is below the half modulus (so
`signedValue = toNat < 2^width`). -/
theorem sIntNNonNegativeValueIsBounded {width : Nat} (value : SIntN (width + 1))
    (isNonNegative : value.isNegative = false) :
    value.bits.toNat < 2 ^ width :=
  fwsLtOfDoubleLtDouble
    (Nat.lt_of_lt_of_le (fwsDoubleLtOfBitVecNonNegative isNonNegative)
      (Nat.le_of_eq fwsDoublePow.symm))

/-- Top bit set ⟹ the raw reading reaches the half modulus (so
`signedValue = toNat - 2^(width+1) ≥ -2^width`, i.e. the complement magnitude
`2^(width+1) - toNat` is at most `2^width`). -/
theorem sIntNNegativeValueIsBounded {width : Nat} (value : SIntN (width + 1))
    (isNegative : value.isNegative = true) :
    2 ^ width ≤ value.bits.toNat :=
  fwsLeOfDoubleLeDouble
    (Nat.le_trans (Nat.le_of_eq fwsDoublePow) (fwsDoubleGeOfBitVecNegative isNegative))

/-- The signed value lies in the two's-complement window: the case-split range
lemma promised by `Views`, phrased subtraction-free in the encoding as
`[-2^width, 2^width)` at carrier width `width + 1`. -/
theorem sIntNValueIsBounded {width : Nat} (value : SIntN (width + 1)) :
    (value.isNegative = false → value.bits.toNat < 2 ^ width)
    ∧ (value.isNegative = true → 2 ^ width ≤ value.bits.toNat) :=
  ⟨sIntNNonNegativeValueIsBounded value, sIntNNegativeValueIsBounded value⟩

/-- Anchor: with the top bit clear, `signedValue` IS the raw reading (pure
`congrArg` over the sign flag; no `Int` lemma touched). -/
theorem sIntNSignedValueOfNonNegative {width : Nat} (value : SIntN width)
    (isNonNegative : value.isNegative = false) :
    value.signedValue = Int.ofNat value.bits.toNat :=
  congrArg
    (fun flag =>
      if flag then Int.ofNat value.bits.toNat - Int.ofNat (2 ^ width)
      else Int.ofNat value.bits.toNat)
    isNonNegative

/-- Anchor: with the top bit set, `signedValue` is the raw reading shifted down
by one modulus (pure `congrArg` over the sign flag). -/
theorem sIntNSignedValueOfNegative {width : Nat} (value : SIntN width)
    (isNegative : value.isNegative = true) :
    value.signedValue = Int.ofNat value.bits.toNat - Int.ofNat (2 ^ width) :=
  congrArg
    (fun flag =>
      if flag then Int.ofNat value.bits.toNat - Int.ofNat (2 ^ width)
      else Int.ofNat value.bits.toNat)
    isNegative

/-! ## The biased interpretation

`sIntNBiasedValue value = signedValue value + 2^width` as a `Nat` — the signed
window `[-2^width, 2^width)` becomes `[0, 2^(width+1))`, and all signed
overflow tests become `Nat` comparisons. -/

/-- Biased readout: the signed value shifted up by the half modulus. -/
def sIntNBiasedValue {width : Nat} (value : SIntN (width + 1)) : Nat :=
  cond value.isNegative
    (value.bits.toNat - 2 ^ width)
    (value.bits.toNat + 2 ^ width)

/-- Top bit clear: the biased value is the raw reading plus the half modulus. -/
theorem sIntNBiasedValueOfNonNegative {width : Nat} (value : SIntN (width + 1))
    (isNonNegative : value.isNegative = false) :
    sIntNBiasedValue value = value.bits.toNat + 2 ^ width :=
  congrArg
    (fun flag => cond flag
      (value.bits.toNat - 2 ^ width) (value.bits.toNat + 2 ^ width))
    isNonNegative

/-- Top bit set: the biased value is the complement magnitude, characterized
additively — `biased + 2^width = toNat`. -/
theorem sIntNBiasedValueOfNegative {width : Nat} (value : SIntN (width + 1))
    (isNegative : value.isNegative = true) :
    sIntNBiasedValue value + 2 ^ width = value.bits.toNat :=
  let landsOnComplement :
      sIntNBiasedValue value = value.bits.toNat - 2 ^ width :=
    congrArg
      (fun flag => cond flag
        (value.bits.toNat - 2 ^ width) (value.bits.toNat + 2 ^ width))
      isNegative
  (congrArg (fun magnitude => magnitude + 2 ^ width) landsOnComplement).trans
    ((Nat.add_comm (value.bits.toNat - 2 ^ width) (2 ^ width)).trans
      (natAddSubOfLe (sIntNNegativeValueIsBounded value isNegative)))

/-- The biased value lives in `[0, 2^(width+1))` — the whole-window bound. -/
theorem sIntNBiasedValueIsBounded {width : Nat} (value : SIntN (width + 1)) :
    sIntNBiasedValue value < 2 ^ (width + 1) :=
  match fwsFlagIsTrueOrFalse value.isNegative with
  | .inl isNegative =>
      Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.le_add_right (sIntNBiasedValue value) (2 ^ width))
          (Nat.le_of_eq (sIntNBiasedValueOfNegative value isNegative)))
        value.bits.isLt
  | .inr isNonNegative =>
      Nat.lt_of_le_of_lt (Nat.le_of_eq (sIntNBiasedValueOfNonNegative value isNonNegative))
        (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_right (sIntNNonNegativeValueIsBounded value isNonNegative)
            (2 ^ width))
          (Nat.le_of_eq fwsHalfAddHalf))

/-- The biased-window encode lemma, shared by every signed exactness claim:
reducing `encoded ∈ [2^width, 2^width + 2^(width+1))` into the carrier and
reading the biased value back recovers `encoded - 2^width`, stated additively.
In signed terms `encoded = trueValue + 2^(width+1)` encodes the in-window
`trueValue` exactly. -/
theorem sIntNEncodeBiasedWindow {width : Nat} {encoded : Nat}
    (lowFits : 2 ^ width ≤ encoded)
    (highFits : encoded < 2 ^ width + 2 ^ (width + 1)) :
    sIntNBiasedValue (⟨bitVecOfNatMod encoded⟩ : SIntN (width + 1)) + 2 ^ width
      = encoded :=
  let payload : SIntN (width + 1) := ⟨bitVecOfNatMod encoded⟩
  let modulusPositive : 0 < 2 ^ (width + 1) := Nat.two_pow_pos (width + 1)
  match Nat.lt_or_ge encoded (2 ^ (width + 1)) with
  | .inl belowModulus =>
      let readNat : payload.bits.toNat = encoded :=
        (bitVecOfNatModToNat encoded).trans (natRemainderOfLt belowModulus)
      let signAbove : 2 ^ (width + 1) ≤ 2 * payload.bits.toNat :=
        Nat.le_trans (Nat.le_of_eq fwsDoublePow.symm)
          (Nat.le_trans (fwsDoubleLeDoubleOfLe lowFits)
            (Nat.le_of_eq (congrArg (fun readout => 2 * readout) readNat.symm)))
      let isNegativePayload : payload.isNegative = true :=
        fwsBitVecIsNegativeEqTrueOfDoubleGe signAbove
      (sIntNBiasedValueOfNegative payload isNegativePayload).trans readNat
  | .inr aboveModulus =>
      let splitEq : 2 ^ (width + 1) + (encoded - 2 ^ (width + 1)) = encoded :=
        natAddSubOfLe aboveModulus
      let restBelowHalf : encoded - 2 ^ (width + 1) < 2 ^ width :=
        Nat.lt_of_add_lt_add_left
          (Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.le_of_eq splitEq) highFits)
            (Nat.le_of_eq (Nat.add_comm (2 ^ width) (2 ^ (width + 1)))))
      let readNat : payload.bits.toNat = encoded - 2 ^ (width + 1) :=
        (bitVecOfNatModToNat encoded).trans
          ((congrArg (fun total => natRemainder total (2 ^ (width + 1)))
              splitEq.symm).trans
            ((natRemainderAddPush (2 ^ (width + 1)) (encoded - 2 ^ (width + 1))
                (2 ^ (width + 1)) modulusPositive).symm.trans
              ((congrArg
                  (fun leading =>
                    natRemainder (leading + (encoded - 2 ^ (width + 1))) (2 ^ (width + 1)))
                  (natRemainderSelf modulusPositive)).trans
                ((congrArg (fun summed => natRemainder summed (2 ^ (width + 1)))
                    (Nat.zero_add (encoded - 2 ^ (width + 1)))).trans
                  (natRemainderOfLt
                    (Nat.lt_of_lt_of_le restBelowHalf
                      (Nat.le_of_lt fwsHalfLtModulus)))))))
      let signBelow : 2 * payload.bits.toNat < 2 ^ (width + 1) :=
        Nat.lt_of_le_of_lt (Nat.le_of_eq (congrArg (fun readout => 2 * readout) readNat))
          (Nat.lt_of_lt_of_le (fwsDoubleLtDoubleOfLt restBelowHalf)
            (Nat.le_of_eq fwsDoublePow))
      let isNonNegativePayload : payload.isNegative = false :=
        fwsBitVecIsNegativeEqFalseOfDoubleLt signBelow
      (congrArg (fun magnitude => magnitude + 2 ^ width)
          (sIntNBiasedValueOfNonNegative payload isNonNegativePayload)).trans
        ((congrArg (fun readout => (readout + 2 ^ width) + 2 ^ width) readNat).trans
          ((Nat.add_assoc (encoded - 2 ^ (width + 1)) (2 ^ width) (2 ^ width)).trans
            ((congrArg (fun halves => (encoded - 2 ^ (width + 1)) + halves)
                fwsHalfAddHalf).trans
              ((Nat.add_comm (encoded - 2 ^ (width + 1)) (2 ^ (width + 1))).trans
                splitEq))))

/-! ## The window ends (the saturate clamp targets) -/

/-- The most negative signed value: bit pattern `10…0`, i.e. `-2^width` at
carrier width `width + 1`. -/
def sIntNMostNegative {width : Nat} : SIntN (width + 1) :=
  ⟨bitVecOfNatMod (2 ^ width)⟩

/-- The most positive signed value: bit pattern `01…1`, i.e. `2^width - 1`
at carrier width `width + 1`. -/
def sIntNMostPositive {width : Nat} : SIntN (width + 1) :=
  ⟨bitVecOfNatMod (2 ^ width - 1)⟩

/-- The most negative value reads back as exactly the half modulus. -/
theorem sIntNMostNegativeToNat {width : Nat} :
    (sIntNMostNegative (width := width)).bits.toNat = 2 ^ width :=
  (bitVecOfNatModToNat (2 ^ width)).trans (natRemainderOfLt fwsHalfLtModulus)

/-- The most negative value has its sign bit set. -/
theorem sIntNMostNegativeIsNegative {width : Nat} :
    (sIntNMostNegative (width := width)).isNegative = true :=
  fwsBitVecIsNegativeEqTrueOfDoubleGe
    (Nat.le_of_eq (fwsDoublePow.symm.trans
      (congrArg (fun readout => 2 * readout) sIntNMostNegativeToNat.symm)))

/-- The most negative value sits at the bottom of the biased window. -/
theorem sIntNMostNegativeBiasedValue {width : Nat} :
    sIntNBiasedValue (sIntNMostNegative (width := width)) = 0 :=
  natAddLeftCancel
    ((Nat.add_comm (2 ^ width) (sIntNBiasedValue sIntNMostNegative)).trans
      ((sIntNBiasedValueOfNegative sIntNMostNegative sIntNMostNegativeIsNegative).trans
        sIntNMostNegativeToNat))

/-- The most positive value reads back as the half modulus' predecessor, stated
additively: `toNat + 1 = 2^width`. -/
theorem sIntNMostPositiveToNatSucc {width : Nat} :
    (sIntNMostPositive (width := width)).bits.toNat + 1 = 2 ^ width :=
  (congrArg (fun readout => readout + 1)
      ((bitVecOfNatModToNat (2 ^ width - 1)).trans
        (natRemainderOfLt (valueBelowWiderModulus maxUnsignedBelowModulus)))).trans
    ((Nat.add_comm (2 ^ width - 1) 1).trans (natAddSubOfLe (Nat.two_pow_pos width)))

/-- The most positive value has its sign bit clear. -/
theorem sIntNMostPositiveIsNegative {width : Nat} :
    (sIntNMostPositive (width := width)).isNegative = false :=
  fwsBitVecIsNegativeEqFalseOfDoubleLt
    (Nat.lt_of_lt_of_le
      (Nat.succ_le_succ (Nat.le_succ (2 * (sIntNMostPositive (width := width)).bits.toNat)))
      (Nat.le_of_eq
        ((congrArg (fun bumped => 2 * bumped) sIntNMostPositiveToNatSucc).trans
          fwsDoublePow)))

/-- The most positive value sits at the top of the biased window, stated
additively: `biased + 1 = 2^(width+1)`. -/
theorem sIntNMostPositiveBiasedValueSucc {width : Nat} :
    sIntNBiasedValue (sIntNMostPositive (width := width)) + 1 = 2 ^ (width + 1) :=
  (congrArg (fun magnitude => magnitude + 1)
      (sIntNBiasedValueOfNonNegative sIntNMostPositive sIntNMostPositiveIsNegative)).trans
    ((Nat.add_assoc (sIntNMostPositive (width := width)).bits.toNat (2 ^ width) 1).trans
      ((congrArg (fun tail => (sIntNMostPositive (width := width)).bits.toNat + tail)
          (Nat.add_comm (2 ^ width) 1)).trans
        (((Nat.add_assoc (sIntNMostPositive (width := width)).bits.toNat 1
            (2 ^ width)).symm).trans
          ((congrArg (fun head => head + 2 ^ width) sIntNMostPositiveToNatSucc).trans
            fwsHalfAddHalf))))

/-! ## Signed trap (add, mul)

Fits tests in biased coordinates: the exact signed sum `s1 + s2` fits the
window iff `2^width ≤ b1 + b2 < 2^width + 2^(width+1)` (since
`b1 + b2 = s1 + s2 + 2^(width+1)`); the exact signed product fits iff
`cross ≤ shifted + 2^width` and `shifted < cross + 2^width` (since
`s1*s2 = shifted - cross`). -/

/-- The in-window sum payload: reduce `b1 + b2` into the carrier (this is
`s1 + s2 + 2^(width+1)`, so `mod 2^(width+1)` it encodes the exact sum). -/
def sIntNAddBiasedEncode {width : Nat} (left right : SIntN (width + 1)) :
    SIntN (width + 1) :=
  ⟨bitVecOfNatMod (sIntNBiasedValue left + sIntNBiasedValue right)⟩

/-- Signed trapping addition: `some` of the exact sum's encoding when the
signed sum fits the window, `none` on signed overflow (either side). -/
def sIntNTrapAdd {width : Nat} (left right : SIntN (width + 1)) :
    Option (SIntN (width + 1)) :=
  cond (Nat.ble (2 ^ width) (sIntNBiasedValue left + sIntNBiasedValue right)
      && Nat.blt (sIntNBiasedValue left + sIntNBiasedValue right)
        (2 ^ width + 2 ^ (width + 1)))
    (some (sIntNAddBiasedEncode left right))
    none

/-- Trap add returns `some` exactly on the signed window. -/
theorem sIntNTrapAddFits {width : Nat} (left right : SIntN (width + 1))
    (lowFits : 2 ^ width ≤ sIntNBiasedValue left + sIntNBiasedValue right)
    (highFits : sIntNBiasedValue left + sIntNBiasedValue right
      < 2 ^ width + 2 ^ (width + 1)) :
    sIntNTrapAdd left right = some (sIntNAddBiasedEncode left right) :=
  (congrArg
      (fun flag => cond
        (flag && Nat.blt (sIntNBiasedValue left + sIntNBiasedValue right)
          (2 ^ width + 2 ^ (width + 1)))
        (some (sIntNAddBiasedEncode left right)) none)
      (natBleEqTrueOfLe lowFits)).trans
    (congrArg
      (fun flag => cond flag (some (sIntNAddBiasedEncode left right)) none)
      (natBltEqTrueOfLt highFits))

/-- Trap add returns `none` on negative overflow (`s1 + s2 < -2^width`). -/
theorem sIntNTrapAddOverflowsBelow {width : Nat} (left right : SIntN (width + 1))
    (underflows : sIntNBiasedValue left + sIntNBiasedValue right < 2 ^ width) :
    sIntNTrapAdd left right = none :=
  congrArg
    (fun flag => cond
      (flag && Nat.blt (sIntNBiasedValue left + sIntNBiasedValue right)
        (2 ^ width + 2 ^ (width + 1)))
      (some (sIntNAddBiasedEncode left right)) none)
    (natBleEqFalseOfLt underflows)

/-- Trap add returns `none` on positive overflow (`2^width ≤ s1 + s2`). -/
theorem sIntNTrapAddOverflowsAbove {width : Nat} (left right : SIntN (width + 1))
    (overflows : 2 ^ width + 2 ^ (width + 1)
      ≤ sIntNBiasedValue left + sIntNBiasedValue right) :
    sIntNTrapAdd left right = none :=
  (congrArg
      (fun flag => cond
        (flag && Nat.blt (sIntNBiasedValue left + sIntNBiasedValue right)
          (2 ^ width + 2 ^ (width + 1)))
        (some (sIntNAddBiasedEncode left right)) none)
      (natBleEqTrueOfLe
        (Nat.le_trans (Nat.le_add_right (2 ^ width) (2 ^ (width + 1))) overflows))).trans
    (congrArg
      (fun flag => cond flag (some (sIntNAddBiasedEncode left right)) none)
      (natBltEqFalseOfLe overflows))

/-- The trap-add payload is the exact signed sum, as the subtraction-free
biased equation `biased(payload) + 2^width = biased(left) + biased(right)`
(i.e. `signed(payload) = s1 + s2` after unshifting both sides). -/
theorem sIntNTrapAddSomeIsExact {width : Nat} (left right : SIntN (width + 1))
    (lowFits : 2 ^ width ≤ sIntNBiasedValue left + sIntNBiasedValue right)
    (highFits : sIntNBiasedValue left + sIntNBiasedValue right
      < 2 ^ width + 2 ^ (width + 1)) :
    sIntNBiasedValue (sIntNAddBiasedEncode left right) + 2 ^ width
      = sIntNBiasedValue left + sIntNBiasedValue right :=
  sIntNEncodeBiasedWindow lowFits highFits

/-- The shifted exact product `b1*b2 + 2^width * 2^width` — the positive part
of `s1*s2` in biased coordinates. -/
def sIntNMulBiasedShiftedProduct {width : Nat} (left right : SIntN (width + 1)) : Nat :=
  sIntNBiasedValue left * sIntNBiasedValue right + 2 ^ width * 2 ^ width

/-- The bias cross-term `2^width * b1 + 2^width * b2` — the negative part of
`s1*s2` in biased coordinates (`s1*s2 = shifted - cross`). -/
def sIntNMulBiasCross {width : Nat} (left right : SIntN (width + 1)) : Nat :=
  2 ^ width * sIntNBiasedValue left + 2 ^ width * sIntNBiasedValue right

/-- The in-window product payload: `(shifted + 2^(width+1)) - cross` is
`s1*s2 + 2^(width+1)` on the fits domain, so its reduction encodes the exact
product. -/
def sIntNMulBiasedEncode {width : Nat} (left right : SIntN (width + 1)) :
    SIntN (width + 1) :=
  ⟨bitVecOfNatMod ((sIntNMulBiasedShiftedProduct left right + 2 ^ (width + 1))
    - sIntNMulBiasCross left right)⟩

/-- Signed trapping multiplication: `some` of the exact product's encoding
when the signed product fits the window, `none` on signed overflow. -/
def sIntNTrapMul {width : Nat} (left right : SIntN (width + 1)) :
    Option (SIntN (width + 1)) :=
  cond (Nat.ble (sIntNMulBiasCross left right)
        (sIntNMulBiasedShiftedProduct left right + 2 ^ width)
      && Nat.blt (sIntNMulBiasedShiftedProduct left right)
        (sIntNMulBiasCross left right + 2 ^ width))
    (some (sIntNMulBiasedEncode left right))
    none

/-- Trap mul returns `some` exactly on the signed window. -/
theorem sIntNTrapMulFits {width : Nat} (left right : SIntN (width + 1))
    (lowFits : sIntNMulBiasCross left right
      ≤ sIntNMulBiasedShiftedProduct left right + 2 ^ width)
    (highFits : sIntNMulBiasedShiftedProduct left right
      < sIntNMulBiasCross left right + 2 ^ width) :
    sIntNTrapMul left right = some (sIntNMulBiasedEncode left right) :=
  (congrArg
      (fun flag => cond
        (flag && Nat.blt (sIntNMulBiasedShiftedProduct left right)
          (sIntNMulBiasCross left right + 2 ^ width))
        (some (sIntNMulBiasedEncode left right)) none)
      (natBleEqTrueOfLe lowFits)).trans
    (congrArg
      (fun flag => cond flag (some (sIntNMulBiasedEncode left right)) none)
      (natBltEqTrueOfLt highFits))

/-- Trap mul returns `none` on negative overflow (`s1*s2 < -2^width`). -/
theorem sIntNTrapMulOverflowsBelow {width : Nat} (left right : SIntN (width + 1))
    (underflows : sIntNMulBiasedShiftedProduct left right + 2 ^ width
      < sIntNMulBiasCross left right) :
    sIntNTrapMul left right = none :=
  congrArg
    (fun flag => cond
      (flag && Nat.blt (sIntNMulBiasedShiftedProduct left right)
        (sIntNMulBiasCross left right + 2 ^ width))
      (some (sIntNMulBiasedEncode left right)) none)
    (natBleEqFalseOfLt underflows)

/-- Trap mul returns `none` on positive overflow (`2^width ≤ s1*s2`). -/
theorem sIntNTrapMulOverflowsAbove {width : Nat} (left right : SIntN (width + 1))
    (overflows : sIntNMulBiasCross left right + 2 ^ width
      ≤ sIntNMulBiasedShiftedProduct left right) :
    sIntNTrapMul left right = none :=
  (congrArg
      (fun flag => cond
        (flag && Nat.blt (sIntNMulBiasedShiftedProduct left right)
          (sIntNMulBiasCross left right + 2 ^ width))
        (some (sIntNMulBiasedEncode left right)) none)
      (natBleEqTrueOfLe
        (Nat.le_trans
          (Nat.le_trans (Nat.le_add_right (sIntNMulBiasCross left right) (2 ^ width))
            overflows)
          (Nat.le_add_right (sIntNMulBiasedShiftedProduct left right) (2 ^ width))))).trans
    (congrArg
      (fun flag => cond flag (some (sIntNMulBiasedEncode left right)) none)
      (natBltEqFalseOfLe overflows))

/-- The trap-mul payload is the exact signed product, as the subtraction-free
`Nat` combination `(biased(payload) + 2^width) + cross = shifted + 2^(width+1)`;
unshifting gives `signed(payload) = s1*s2 = shifted - cross`. -/
theorem sIntNTrapMulSomeIsExact {width : Nat} (left right : SIntN (width + 1))
    (lowFits : sIntNMulBiasCross left right
      ≤ sIntNMulBiasedShiftedProduct left right + 2 ^ width)
    (highFits : sIntNMulBiasedShiftedProduct left right
      < sIntNMulBiasCross left right + 2 ^ width) :
    (sIntNBiasedValue (sIntNMulBiasedEncode left right) + 2 ^ width)
        + sIntNMulBiasCross left right
      = sIntNMulBiasedShiftedProduct left right + 2 ^ (width + 1) :=
  let crossLeTotal : sIntNMulBiasCross left right
      ≤ sIntNMulBiasedShiftedProduct left right + 2 ^ (width + 1) :=
    Nat.le_trans lowFits
      (Nat.add_le_add_left (Nat.le_of_lt fwsHalfLtModulus)
        (sIntNMulBiasedShiftedProduct left right))
  let splitEq : sIntNMulBiasCross left right
        + ((sIntNMulBiasedShiftedProduct left right + 2 ^ (width + 1))
          - sIntNMulBiasCross left right)
      = sIntNMulBiasedShiftedProduct left right + 2 ^ (width + 1) :=
    natAddSubOfLe crossLeTotal
  let lowWindow : 2 ^ width
      ≤ (sIntNMulBiasedShiftedProduct left right + 2 ^ (width + 1))
        - sIntNMulBiasCross left right :=
    fwsLeOfAddLeAddLeft (sharedAddend := sIntNMulBiasCross left right)
      (Nat.le_trans (Nat.add_le_add_right lowFits (2 ^ width))
        (Nat.le_of_eq
          ((Nat.add_assoc (sIntNMulBiasedShiftedProduct left right)
              (2 ^ width) (2 ^ width)).trans
            ((congrArg
                (fun halves => sIntNMulBiasedShiftedProduct left right + halves)
                fwsHalfAddHalf).trans
              splitEq.symm))))
  let highWindow : (sIntNMulBiasedShiftedProduct left right + 2 ^ (width + 1))
        - sIntNMulBiasCross left right
      < 2 ^ width + 2 ^ (width + 1) :=
    Nat.lt_of_add_lt_add_left
      (Nat.lt_of_le_of_lt (Nat.le_of_eq splitEq)
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_right highFits (2 ^ (width + 1)))
          (Nat.le_of_eq
            (Nat.add_assoc (sIntNMulBiasCross left right) (2 ^ width)
              (2 ^ (width + 1))))))
  let encodeExact :
      sIntNBiasedValue (sIntNMulBiasedEncode left right) + 2 ^ width
        = (sIntNMulBiasedShiftedProduct left right + 2 ^ (width + 1))
          - sIntNMulBiasCross left right :=
    sIntNEncodeBiasedWindow lowWindow highWindow
  (congrArg (fun exact => exact + sIntNMulBiasCross left right) encodeExact).trans
    ((Nat.add_comm
        ((sIntNMulBiasedShiftedProduct left right + 2 ^ (width + 1))
          - sIntNMulBiasCross left right)
        (sIntNMulBiasCross left right)).trans
      splitEq)

/-! ## Signed saturate (add, mul)

Clamps to the window ends: below the window to `sIntNMostNegative`
(`-2^width`), above it to `sIntNMostPositive` (`2^width - 1`, stated
additively as `toNat + 1 = 2^width`), exact in range. -/

/-- Signed saturating addition. -/
def sIntNSaturateAdd {width : Nat} (left right : SIntN (width + 1)) :
    SIntN (width + 1) :=
  cond (Nat.blt (sIntNBiasedValue left + sIntNBiasedValue right) (2 ^ width))
    sIntNMostNegative
    (cond (Nat.blt (sIntNBiasedValue left + sIntNBiasedValue right)
        (2 ^ width + 2 ^ (width + 1)))
      (sIntNAddBiasedEncode left right)
      sIntNMostPositive)

/-- In range, saturate add is the exact-sum encoding. -/
theorem sIntNSaturateAddInRange {width : Nat} (left right : SIntN (width + 1))
    (lowFits : 2 ^ width ≤ sIntNBiasedValue left + sIntNBiasedValue right)
    (highFits : sIntNBiasedValue left + sIntNBiasedValue right
      < 2 ^ width + 2 ^ (width + 1)) :
    sIntNSaturateAdd left right = sIntNAddBiasedEncode left right :=
  (congrArg
      (fun flag => cond flag sIntNMostNegative
        (cond (Nat.blt (sIntNBiasedValue left + sIntNBiasedValue right)
            (2 ^ width + 2 ^ (width + 1)))
          (sIntNAddBiasedEncode left right)
          sIntNMostPositive))
      (natBltEqFalseOfLe lowFits)).trans
    (congrArg
      (fun flag => cond flag (sIntNAddBiasedEncode left right) sIntNMostPositive)
      (natBltEqTrueOfLt highFits))

/-- In range, saturate add is exact: same biased equation as trap. -/
theorem sIntNSaturateAddInRangeIsExact {width : Nat} (left right : SIntN (width + 1))
    (lowFits : 2 ^ width ≤ sIntNBiasedValue left + sIntNBiasedValue right)
    (highFits : sIntNBiasedValue left + sIntNBiasedValue right
      < 2 ^ width + 2 ^ (width + 1)) :
    sIntNBiasedValue (sIntNSaturateAdd left right) + 2 ^ width
      = sIntNBiasedValue left + sIntNBiasedValue right :=
  (congrArg (fun result => sIntNBiasedValue result + 2 ^ width)
      (sIntNSaturateAddInRange left right lowFits highFits)).trans
    (sIntNTrapAddSomeIsExact left right lowFits highFits)

/-- On negative overflow, saturate add clamps to the most negative value. -/
theorem sIntNSaturateAddClampsLow {width : Nat} (left right : SIntN (width + 1))
    (underflows : sIntNBiasedValue left + sIntNBiasedValue right < 2 ^ width) :
    sIntNSaturateAdd left right = sIntNMostNegative :=
  congrArg
    (fun flag => cond flag sIntNMostNegative
      (cond (Nat.blt (sIntNBiasedValue left + sIntNBiasedValue right)
          (2 ^ width + 2 ^ (width + 1)))
        (sIntNAddBiasedEncode left right)
        sIntNMostPositive))
    (natBltEqTrueOfLt underflows)

/-- On positive overflow, saturate add clamps to the most positive value. -/
theorem sIntNSaturateAddClampsHigh {width : Nat} (left right : SIntN (width + 1))
    (overflows : 2 ^ width + 2 ^ (width + 1)
      ≤ sIntNBiasedValue left + sIntNBiasedValue right) :
    sIntNSaturateAdd left right = sIntNMostPositive :=
  (congrArg
      (fun flag => cond flag sIntNMostNegative
        (cond (Nat.blt (sIntNBiasedValue left + sIntNBiasedValue right)
            (2 ^ width + 2 ^ (width + 1)))
          (sIntNAddBiasedEncode left right)
          sIntNMostPositive))
      (natBltEqFalseOfLe
        (Nat.le_trans (Nat.le_add_right (2 ^ width) (2 ^ (width + 1))) overflows))).trans
    (congrArg
      (fun flag => cond flag (sIntNAddBiasedEncode left right) sIntNMostPositive)
      (natBltEqFalseOfLe overflows))

/-- Saturate add stays in the biased window on every branch (clamp
correctness, the signed mirror of the unsigned upper-bound leg). -/
theorem sIntNSaturateAddIsBounded {width : Nat} (left right : SIntN (width + 1)) :
    sIntNBiasedValue (sIntNSaturateAdd left right) < 2 ^ (width + 1) :=
  sIntNBiasedValueIsBounded (sIntNSaturateAdd left right)

/-- Signed saturating multiplication. -/
def sIntNSaturateMul {width : Nat} (left right : SIntN (width + 1)) :
    SIntN (width + 1) :=
  cond (Nat.blt (sIntNMulBiasedShiftedProduct left right + 2 ^ width)
      (sIntNMulBiasCross left right))
    sIntNMostNegative
    (cond (Nat.blt (sIntNMulBiasedShiftedProduct left right)
        (sIntNMulBiasCross left right + 2 ^ width))
      (sIntNMulBiasedEncode left right)
      sIntNMostPositive)

/-- In range, saturate mul is the exact-product encoding. -/
theorem sIntNSaturateMulInRange {width : Nat} (left right : SIntN (width + 1))
    (lowFits : sIntNMulBiasCross left right
      ≤ sIntNMulBiasedShiftedProduct left right + 2 ^ width)
    (highFits : sIntNMulBiasedShiftedProduct left right
      < sIntNMulBiasCross left right + 2 ^ width) :
    sIntNSaturateMul left right = sIntNMulBiasedEncode left right :=
  (congrArg
      (fun flag => cond flag sIntNMostNegative
        (cond (Nat.blt (sIntNMulBiasedShiftedProduct left right)
            (sIntNMulBiasCross left right + 2 ^ width))
          (sIntNMulBiasedEncode left right)
          sIntNMostPositive))
      (natBltEqFalseOfLe lowFits)).trans
    (congrArg
      (fun flag => cond flag (sIntNMulBiasedEncode left right) sIntNMostPositive)
      (natBltEqTrueOfLt highFits))

/-- In range, saturate mul is exact: same biased equation as trap. -/
theorem sIntNSaturateMulInRangeIsExact {width : Nat} (left right : SIntN (width + 1))
    (lowFits : sIntNMulBiasCross left right
      ≤ sIntNMulBiasedShiftedProduct left right + 2 ^ width)
    (highFits : sIntNMulBiasedShiftedProduct left right
      < sIntNMulBiasCross left right + 2 ^ width) :
    (sIntNBiasedValue (sIntNSaturateMul left right) + 2 ^ width)
        + sIntNMulBiasCross left right
      = sIntNMulBiasedShiftedProduct left right + 2 ^ (width + 1) :=
  (congrArg
      (fun result => (sIntNBiasedValue result + 2 ^ width)
        + sIntNMulBiasCross left right)
      (sIntNSaturateMulInRange left right lowFits highFits)).trans
    (sIntNTrapMulSomeIsExact left right lowFits highFits)

/-- On negative overflow, saturate mul clamps to the most negative value. -/
theorem sIntNSaturateMulClampsLow {width : Nat} (left right : SIntN (width + 1))
    (underflows : sIntNMulBiasedShiftedProduct left right + 2 ^ width
      < sIntNMulBiasCross left right) :
    sIntNSaturateMul left right = sIntNMostNegative :=
  congrArg
    (fun flag => cond flag sIntNMostNegative
      (cond (Nat.blt (sIntNMulBiasedShiftedProduct left right)
          (sIntNMulBiasCross left right + 2 ^ width))
        (sIntNMulBiasedEncode left right)
        sIntNMostPositive))
    (natBltEqTrueOfLt underflows)

/-- On positive overflow, saturate mul clamps to the most positive value. -/
theorem sIntNSaturateMulClampsHigh {width : Nat} (left right : SIntN (width + 1))
    (overflows : sIntNMulBiasCross left right + 2 ^ width
      ≤ sIntNMulBiasedShiftedProduct left right) :
    sIntNSaturateMul left right = sIntNMostPositive :=
  (congrArg
      (fun flag => cond flag sIntNMostNegative
        (cond (Nat.blt (sIntNMulBiasedShiftedProduct left right)
            (sIntNMulBiasCross left right + 2 ^ width))
          (sIntNMulBiasedEncode left right)
          sIntNMostPositive))
      (natBltEqFalseOfLe
        (Nat.le_trans
          (Nat.le_trans (Nat.le_add_right (sIntNMulBiasCross left right) (2 ^ width))
            overflows)
          (Nat.le_add_right (sIntNMulBiasedShiftedProduct left right) (2 ^ width))))).trans
    (congrArg
      (fun flag => cond flag (sIntNMulBiasedEncode left right) sIntNMostPositive)
      (natBltEqFalseOfLe overflows))

/-- Saturate mul stays in the biased window on every branch. -/
theorem sIntNSaturateMulIsBounded {width : Nat} (left right : SIntN (width + 1)) :
    sIntNBiasedValue (sIntNSaturateMul left right) < 2 ^ (width + 1) :=
  sIntNBiasedValueIsBounded (sIntNSaturateMul left right)

/-! ## Sign extension preserves the signed value

`bitVecSignExtend` branches on the sign bit; the clear branch is the
zero-extension reading, the set branch adds the mask `2^(width+extra) - 2^width`
whose sole reasoning interface is the gated `natAddSubOfLe`. -/

/-- Signed view widening: sign-extend a `SIntN width` to
`SIntN (width + extra)`. -/
def SIntN.signExtend {width : Nat} (value : SIntN width) (extra : Nat) :
    SIntN (width + extra) :=
  ⟨bitVecSignExtend value.bits (width + extra)⟩

/-- Branch selection: with the sign bit clear, sign-extension is the bare
reducer (i.e. zero-extension). -/
theorem fwsBitVecSignExtendOfNonNegative {width newWidth : Nat} {value : BitVec width}
    (isNonNegative : bitVecIsNegative value = false) :
    bitVecSignExtend value newWidth = bitVecOfNatMod value.toNat :=
  congrArg
    (fun flag =>
      if flag then (bitVecOfNatMod (value.toNat + (2 ^ newWidth - 2 ^ width))
        : BitVec newWidth)
      else bitVecOfNatMod value.toNat)
    isNonNegative

/-- Branch selection: with the sign bit set, sign-extension adds the high
mask. -/
theorem fwsBitVecSignExtendOfNegative {width newWidth : Nat} {value : BitVec width}
    (isNegative : bitVecIsNegative value = true) :
    bitVecSignExtend value newWidth
      = bitVecOfNatMod (value.toNat + (2 ^ newWidth - 2 ^ width)) :=
  congrArg
    (fun flag =>
      if flag then (bitVecOfNatMod (value.toNat + (2 ^ newWidth - 2 ^ width))
        : BitVec newWidth)
      else bitVecOfNatMod value.toNat)
    isNegative

/-- Top bit clear: sign extension IS zero extension (bit-identical). -/
theorem sIntNSignExtendNonNegativeMatchesZeroExtend {width : Nat} (value : SIntN width)
    (extra : Nat) (isNonNegative : value.isNegative = false) :
    (value.signExtend extra).bits = bitVecZeroExtend value.bits (width + extra) :=
  fwsBitVecSignExtendOfNonNegative isNonNegative

/-- Top bit clear: sign extension preserves the raw reading (hence the
signed value); this leg reduces to the zero-extension argument. -/
theorem sIntNSignExtendPreservesNonNegativeValue {width : Nat} (value : SIntN width)
    (extra : Nat) (isNonNegative : value.isNegative = false) :
    (value.signExtend extra).bits.toNat = value.bits.toNat :=
  (congrArg BitVec.toNat
      (fwsBitVecSignExtendOfNonNegative (newWidth := width + extra) isNonNegative)).trans
    ((bitVecOfNatModToNat value.bits.toNat).trans
      (natRemainderOfLt (valueBelowWiderModulus value.bits.isLt)))

/-- Top bit set: sign extension preserves the complement magnitude, stated
additively: `extToNat + 2^width = toNat + 2^(width+extra)` (both sides are the
shared magnitude `2^width - toNat = 2^(width+extra) - extToNat` shifted by the
sum of the two moduli, so the signed value is unchanged). -/
theorem sIntNSignExtendPreservesNegativeValue {width : Nat} (value : SIntN width)
    (extra : Nat) (isNegative : value.isNegative = true) :
    (value.signExtend extra).bits.toNat + 2 ^ width
      = value.bits.toNat + 2 ^ (width + extra) :=
  let deltaEq : 2 ^ width + (2 ^ (width + extra) - 2 ^ width) = 2 ^ (width + extra) :=
    natAddSubOfLe fwsPowLeWiderPow
  let rawBelow : value.bits.toNat + (2 ^ (width + extra) - 2 ^ width)
      < 2 ^ (width + extra) :=
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_right value.bits.isLt (2 ^ (width + extra) - 2 ^ width))
      (Nat.le_of_eq deltaEq)
  let extendedEq : (value.signExtend extra).bits.toNat
      = value.bits.toNat + (2 ^ (width + extra) - 2 ^ width) :=
    (congrArg BitVec.toNat
        (fwsBitVecSignExtendOfNegative (newWidth := width + extra) isNegative)).trans
      ((bitVecOfNatModToNat (value.bits.toNat + (2 ^ (width + extra) - 2 ^ width))).trans
        (natRemainderOfLt rawBelow))
  (congrArg (fun readout => readout + 2 ^ width) extendedEq).trans
    ((Nat.add_assoc value.bits.toNat (2 ^ (width + extra) - 2 ^ width)
        (2 ^ width)).trans
      ((congrArg (fun tail => value.bits.toNat + tail)
          (Nat.add_comm (2 ^ (width + extra) - 2 ^ width) (2 ^ width))).trans
        (congrArg (fun tail => value.bits.toNat + tail) deltaEq)))

/-- Sign extension preserves the sign bit. -/
theorem sIntNSignExtendPreservesSign {width : Nat} (value : SIntN width)
    (extra : Nat) :
    (value.signExtend extra).isNegative = value.isNegative :=
  match fwsFlagIsTrueOrFalse value.isNegative with
  | .inr isNonNegative =>
      (fwsBitVecIsNegativeEqFalseOfDoubleLt
        (Nat.lt_of_le_of_lt
          (Nat.le_of_eq (congrArg (fun readout => 2 * readout)
            (sIntNSignExtendPreservesNonNegativeValue value extra isNonNegative)))
          (valueBelowWiderModulus
            (fwsDoubleLtOfBitVecNonNegative isNonNegative)))).trans
        isNonNegative.symm
  | .inl isNegative =>
      let deltaEq : 2 ^ width + (2 ^ (width + extra) - 2 ^ width)
          = 2 ^ (width + extra) :=
        natAddSubOfLe fwsPowLeWiderPow
      let twoMulDeltaGe : (2 ^ (width + extra) - 2 ^ width)
          ≤ 2 * (2 ^ (width + extra) - 2 ^ width) :=
        Nat.le_trans
          (Nat.le_add_right (2 ^ (width + extra) - 2 ^ width)
            (2 ^ (width + extra) - 2 ^ width))
          (Nat.le_of_eq
            ((congrArg (fun head => head + (2 ^ (width + extra) - 2 ^ width))
                (Nat.mul_one (2 ^ (width + extra) - 2 ^ width))).symm.trans
              (Nat.mul_comm (2 ^ (width + extra) - 2 ^ width) 2)))
      let doubledGe : 2 ^ (width + extra)
          ≤ 2 * (value.signExtend extra).bits.toNat :=
        Nat.le_trans (Nat.le_of_eq deltaEq.symm)
          (Nat.le_trans
            (Nat.add_le_add (fwsDoubleGeOfBitVecNegative isNegative) twoMulDeltaGe)
            (Nat.le_of_eq
              ((Nat.left_distrib 2 value.bits.toNat
                  (2 ^ (width + extra) - 2 ^ width)).symm.trans
                (congrArg (fun readout => 2 * readout)
                  ((congrArg BitVec.toNat
                      (fwsBitVecSignExtendOfNegative
                        (newWidth := width + extra) isNegative)).trans
                    ((bitVecOfNatModToNat
                        (value.bits.toNat + (2 ^ (width + extra) - 2 ^ width))).trans
                      (natRemainderOfLt
                        (Nat.lt_of_lt_of_le
                          (Nat.add_lt_add_right value.bits.isLt
                            (2 ^ (width + extra) - 2 ^ width))
                          (Nat.le_of_eq deltaEq))))).symm))))
      (fwsBitVecIsNegativeEqTrueOfDoubleGe doubledGe).trans isNegative.symm

/-! ## The BitVec-to-Decision value bridge

`Decision/BitVectorArithmetic` carries its own little-endian `List Bool`
carrier with the Horner value `bvaToNat`.  The explicit conversion peels the
substrate's `toNat` bit by bit through the structural `natQuotient` /
`natRemainder` pair, avoiding the `>>>`-to-division route (`Nat.shiftRight`
routes through `propext`); the round-trip theorems identify the two value
readings. -/

/-- One dyadic digit as its `bvaBoolToNat` reading: a value below `2` survives
the `== 1` flag round-trip. -/
theorem fwsBoolToNatOfBeqOne : ∀ {bitValue : Nat}, bitValue < 2 →
    bvaBoolToNat (bitValue == 1) = bitValue
  | 0, _isBounded => rfl
  | 1, _isBounded => rfl
  | bitValue + 2, isBounded =>
      nomatch Nat.lt_of_succ_lt_succ
        (Nat.lt_of_succ_lt_succ (isBounded : bitValue + 2 < 2))

/-- Little-endian dyadic expansion with fuel = width: peel `mod 2`, recurse on
the structural quotient. -/
def fwsNatBitsLittleEndian : Nat → Nat → List Bool
  | 0, _value => []
  | width + 1, value =>
      (natRemainder value 2 == 1) :: fwsNatBitsLittleEndian width (natQuotient value 2)

/-- The expansion always has exactly `width` bits. -/
theorem fwsNatBitsLittleEndianLength : ∀ (width value : Nat),
    List.length (fwsNatBitsLittleEndian width value) = width
  | 0, _value => rfl
  | width + 1, value =>
      congrArg (fun tail => tail + 1)
        (fwsNatBitsLittleEndianLength width (natQuotient value 2))

/-- The value round-trip: on the fits domain the Horner reading of the
expansion recovers the value (induction on the width; the head digit is the
structural remainder, the tail is the quotient's expansion). -/
theorem fwsNatBitsLittleEndianToNat : ∀ (width value : Nat), value < 2 ^ width →
    bvaToNat (fwsNatBitsLittleEndian width value) = value
  | 0, _value, isBounded => (natEqZeroOfLeZero (Nat.le_of_succ_le_succ isBounded)).symm
  | width + 1, value, isBounded =>
      let twoIsPositive : 0 < 2 := Nat.succ_le_succ (Nat.zero_le 1)
      let reconstruct :
          value = 2 * natQuotient value 2 + natRemainder value 2 :=
        natRemainderReconstructs value 2
      let remainderBound : natRemainder value 2 < 2 :=
        natRemainderIsBounded twoIsPositive
      let quotientBound : natQuotient value 2 < 2 ^ width :=
        fwsLtOfDoubleLtDouble
          (Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.le_add_right (2 * natQuotient value 2) (natRemainder value 2))
              (Nat.le_of_eq reconstruct.symm))
            (Nat.lt_of_lt_of_le isBounded (Nat.le_of_eq fwsDoublePow.symm)))
      let recursiveReading :
          bvaToNat (fwsNatBitsLittleEndian width (natQuotient value 2))
            = natQuotient value 2 :=
        fwsNatBitsLittleEndianToNat width (natQuotient value 2) quotientBound
      (congrArg
          (fun head => head
            + 2 * bvaToNat (fwsNatBitsLittleEndian width (natQuotient value 2)))
          (fwsBoolToNatOfBeqOne remainderBound)).trans
        ((congrArg (fun tail => natRemainder value 2 + 2 * tail) recursiveReading).trans
          ((Nat.add_comm (natRemainder value 2) (2 * natQuotient value 2)).trans
            reconstruct.symm))

/-- Convert a `BitVec width` to the Decision carrier's little-endian bit list. -/
def fwsBitVecToBvaBits {width : Nat} (value : BitVec width) : List Bool :=
  fwsNatBitsLittleEndian width value.toNat

/-- The conversion has exactly `width` bits. -/
theorem fwsBitVecToBvaBitsLength {width : Nat} (value : BitVec width) :
    List.length (fwsBitVecToBvaBits value) = width :=
  fwsNatBitsLittleEndianLength width value.toNat

/-- The two value readings agree: `bvaToNat` of the conversion is
`BitVec.toNat` (the `isLt` bound feeds the fits domain). -/
theorem fwsBitVecToBvaBitsToNat {width : Nat} (value : BitVec width) :
    bvaToNat (fwsBitVecToBvaBits value) = value.toNat :=
  fwsNatBitsLittleEndianToNat width value.toNat value.isLt

/-- Full round-trip: reducing the Horner reading back into the substrate
recovers the original vector. -/
theorem fwsBitVecToBvaBitsRoundTrip {width : Nat} (value : BitVec width) :
    (bitVecOfNatMod (bvaToNat (fwsBitVecToBvaBits value)) : BitVec width) = value :=
  BitVec.eq_of_toNat_eq
    ((bitVecOfNatModToNat (bvaToNat (fwsBitVecToBvaBits value))).trans
      ((congrArg (fun reading => natRemainder reading (2 ^ width))
          (fwsBitVecToBvaBitsToNat value)).trans
        (natRemainderOfLt value.isLt)))

/-- Subsystem marker for the fixed-width signed semantics: signed range, signed
trap add/mul, signed saturate add/mul, sign-extension value preservation, and
the `bvaToNat`-versus-`BitVec.toNat` value bridge with its full round-trip are
all established zero-axiom in this file. -/
def fxNumZFixed_hasSignedSemantics : Bool := true

/-! ## Smoke tests (interpretation via `signedValue`, refutation cases included)

Add and saturate at width 8: `100 + 27 = 127` fits; `100 + 28 = 128` overflows;
`(-100) + (-28) = -128` fits exactly at the window floor; `(-100) + (-29)`
overflows; saturate clamps the same pairs to `127` and `-128`.

The structural `natRemainder` counts the dividend down one unit per recursion,
and `lake build` runs `#eval` in the interpreter with the default stack
(about 8k frames), so the in-file mul and extension smokes use small carriers:
mul at width 6 (window `[-32, 32)`, bias shift `32 * 32 = 1024` frames) with
`7 * 4 = 28` fitting, `7 * 5 = 35` overflowing, `(-8) * 4 = -32` at the floor,
`(-8) * 5` overflowing; extension from width `8` to `12` (`-1` and `5`
preserved, raw depth `4095`).  The width-8 mul and width `8` to `16` extension
checks (bias shift `16384`, all-ones `65535`, beyond the default interpreter
stack) run in the verification probe under `lean --tstack=500000` with the same
expressions. -/

#eval (sIntNTrapAdd (SIntN.ofNat 100 : i8) (SIntN.ofNat 27)).map SIntN.signedValue
#eval (sIntNTrapAdd (SIntN.ofNat 100 : i8) (SIntN.ofNat 28)).map SIntN.signedValue
#eval (sIntNTrapAdd (SIntN.ofNat 156 : i8) (SIntN.ofNat 228)).map SIntN.signedValue
#eval (sIntNTrapAdd (SIntN.ofNat 156 : i8) (SIntN.ofNat 227)).map SIntN.signedValue
#eval (sIntNSaturateAdd (SIntN.ofNat 100 : i8) (SIntN.ofNat 28)).signedValue
#eval (sIntNSaturateAdd (SIntN.ofNat 156 : i8) (SIntN.ofNat 227)).signedValue
#eval (sIntNSaturateAdd (SIntN.ofNat 50 : i8) (SIntN.ofNat 20)).signedValue
#eval (sIntNTrapMul (SIntN.ofNat 7 : SIntN 6) (SIntN.ofNat 4)).map SIntN.signedValue
#eval (sIntNTrapMul (SIntN.ofNat 7 : SIntN 6) (SIntN.ofNat 5)).map SIntN.signedValue
#eval (sIntNTrapMul (SIntN.ofNat 56 : SIntN 6) (SIntN.ofNat 4)).map SIntN.signedValue
#eval (sIntNTrapMul (SIntN.ofNat 56 : SIntN 6) (SIntN.ofNat 5)).map SIntN.signedValue
#eval (sIntNSaturateMul (SIntN.ofNat 7 : SIntN 6) (SIntN.ofNat 5)).signedValue
#eval (sIntNSaturateMul (SIntN.ofNat 56 : SIntN 6) (SIntN.ofNat 5)).signedValue
#eval ((SIntN.ofNat 255 : i8).signExtend 4).signedValue
#eval ((SIntN.ofNat 255 : i8).signExtend 4).bits.toNat
#eval ((SIntN.ofNat 5 : i8).signExtend 4).signedValue
#eval bvaToNat (fwsBitVecToBvaBits (SIntN.ofNat 156 : i8).bits)
#eval fwsBitVecToBvaBits (SIntN.ofNat 156 : i8).bits
-- Refutation cases: wrong-value comparisons must evaluate to false.
#eval bvaToNat (fwsBitVecToBvaBits (SIntN.ofNat 156 : i8).bits) == 155
#eval (sIntNTrapAdd (SIntN.ofNat 100 : i8) (SIntN.ofNat 27)).map SIntN.signedValue
  == some 128
#eval (sIntNSaturateAdd (SIntN.ofNat 100 : i8) (SIntN.ofNat 28)).signedValue
  == (-127 : Int)
#eval ((SIntN.ofNat 255 : i8).signExtend 4).signedValue == (255 : Int)

end FX1Poly.ComputerAlgebra
