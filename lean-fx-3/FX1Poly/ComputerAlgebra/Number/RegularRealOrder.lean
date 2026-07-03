import FX1Poly.ComputerAlgebra.Number.RegularRealMultiplication

/-! # RegularReal order — the positivity core (NUM-R-4a)

The ℝ order is APARTNESS-FIRST and its strict relations CARRY DATA: a
positivity claim is a `Type`-valued witness structure, not a `Prop`-level
existential — downstream constructions (the inverse on apartness, R-5)
must COMPUTE from the witness index, and Lean's `Prop`-existentials do not
project.  Locked decisions:

  * **Positivity = a doubled margin at one index**: `x` is positive when
    some approximant clears `2/(w+1)`.  The doubling is what makes the
    witness QUANTITATIVE: regularity can eat one `1/(w+1)` of it and still
    leave `1/(2w+2)` at every index past `2w+1` (the tail lemma).
  * The bound `≤` is used, not `<` — the margin already carries the
    strictness, and `≤` is the decidable-per-index form.
  * Setoid transport re-witnesses at the QUADRUPLED index, where the
    margin arithmetic is EXACT (two doubling identities, no estimates).

The enabling ℚ kit shipped here: shunting (`a − b ≤ c → a ≤ b + c`) and
the shared-addend CANCELLATION on the order — the two fundamental moves
the corpus was still missing. -/

namespace FX1Poly.ComputerAlgebra

namespace RationalPair

/-- Every value sits below its double plus one — the additive witness is
itself plus one, after unfolding the double. -/
theorem natSelfLeDoubleSelfSucc (value : Nat) : value ≤ 2 * value + 1 :=
  have doubleUnfolds : 2 * value = value + value :=
    (Nat.succ_mul 1 value).trans
      (congrArg (· + value)
        ((Nat.mul_comm 1 value).trans (Nat.zero_add value)))
  Nat.le.intro (k := value + 1) (congrArg (· + 1) doubleUnfolds.symm)

/-- **Shunting**: a bounded difference moves across the order — from
`high − low ≤ bound` conclude `high ≤ low + bound`.  The recovery identity
`low + (high − low) ~ high` feeds one monotone step. -/
theorem lessEqualAsAddOfSubLessEqual {highValue lowValue bound : RationalPair}
    (isDiffBounded : LessEqualAs (subExact highValue lowValue) bound) :
    LessEqualAs highValue (addExact lowValue bound) :=
  lessEqualAsCongrLeft (addExactSubExactCancelDenotesSame lowValue highValue)
    (addExactMonotone (lessEqualAsRefl lowValue) isDiffBounded)

/-- **Shared-addend cancellation on the order**: `l + s ≤ r + s → l ≤ r`.
Cross-multiplication distributes both sides; the shared summand's
cross-products are EQUAL after a middle swap and cancel additively; the
remaining products share the positive square of the shared denominator,
which cancels multiplicatively. -/
theorem lessEqualAsAddRightCancel {leftValue rightValue sharedValue : RationalPair}
    (isShiftedBelow : LessEqualAs (addExact leftValue sharedValue)
      (addExact rightValue sharedValue)) :
    LessEqualAs leftValue rightValue :=
  have leftExpands :
      (leftValue.numerator * denominatorInt sharedValue +
          sharedValue.numerator * denominatorInt leftValue) *
        (denominatorInt rightValue * denominatorInt sharedValue) =
      leftValue.numerator * denominatorInt rightValue *
          (denominatorInt sharedValue * denominatorInt sharedValue) +
        sharedValue.numerator * denominatorInt rightValue *
          (denominatorInt leftValue * denominatorInt sharedValue) :=
    (intRightDistrib (leftValue.numerator * denominatorInt sharedValue)
        (sharedValue.numerator * denominatorInt leftValue)
        (denominatorInt rightValue * denominatorInt sharedValue)).trans
      ((congrArg
          (· + sharedValue.numerator * denominatorInt leftValue *
            (denominatorInt rightValue * denominatorInt sharedValue))
          (intMulSwapMiddle leftValue.numerator (denominatorInt sharedValue)
            (denominatorInt rightValue) (denominatorInt sharedValue))).trans
        (congrArg
          (leftValue.numerator * denominatorInt rightValue *
            (denominatorInt sharedValue * denominatorInt sharedValue) + ·)
          (intMulSwapMiddle sharedValue.numerator (denominatorInt leftValue)
            (denominatorInt rightValue) (denominatorInt sharedValue))))
  have rightExpands :
      (rightValue.numerator * denominatorInt sharedValue +
          sharedValue.numerator * denominatorInt rightValue) *
        (denominatorInt leftValue * denominatorInt sharedValue) =
      rightValue.numerator * denominatorInt leftValue *
          (denominatorInt sharedValue * denominatorInt sharedValue) +
        sharedValue.numerator * denominatorInt rightValue *
          (denominatorInt leftValue * denominatorInt sharedValue) :=
    (intRightDistrib (rightValue.numerator * denominatorInt sharedValue)
        (sharedValue.numerator * denominatorInt rightValue)
        (denominatorInt leftValue * denominatorInt sharedValue)).trans
      (congrArg
        (· + sharedValue.numerator * denominatorInt rightValue *
          (denominatorInt leftValue * denominatorInt sharedValue))
        (intMulSwapMiddle rightValue.numerator (denominatorInt sharedValue)
          (denominatorInt leftValue) (denominatorInt sharedValue)))
  have shiftedShared :
      sharedValue.numerator * denominatorInt rightValue *
          (denominatorInt leftValue * denominatorInt sharedValue) +
        leftValue.numerator * denominatorInt rightValue *
          (denominatorInt sharedValue * denominatorInt sharedValue) ≤
      sharedValue.numerator * denominatorInt rightValue *
          (denominatorInt leftValue * denominatorInt sharedValue) +
        rightValue.numerator * denominatorInt leftValue *
          (denominatorInt sharedValue * denominatorInt sharedValue) :=
    intLessEqualOfEqLeft
      (intAddComm
        (sharedValue.numerator * denominatorInt rightValue *
          (denominatorInt leftValue * denominatorInt sharedValue))
        (leftValue.numerator * denominatorInt rightValue *
          (denominatorInt sharedValue * denominatorInt sharedValue)))
      (intLessEqualOfEqRight
        (intLessEqualOfEqLeft leftExpands.symm
          (intLessEqualOfEqRight isShiftedBelow rightExpands))
        (intAddComm
          (rightValue.numerator * denominatorInt leftValue *
            (denominatorInt sharedValue * denominatorInt sharedValue))
          (sharedValue.numerator * denominatorInt rightValue *
            (denominatorInt leftValue * denominatorInt sharedValue))))
  intLeOfMulLeMulRightOfPos
    (intMulPos (denominatorIntIsPositive sharedValue)
      (denominatorIntIsPositive sharedValue))
    (intAddLeftCancelLessEqual shiftedShared)

/-- The reciprocal splits into FOUR copies at the twice-doubled index —
two doubling identities composed; the margin transport's exact arithmetic. -/
theorem reciprocalQuadrupleSplitDenotesSame (baseIndex : Nat) :
    DenotesSameAs (reciprocalOfSucc baseIndex)
      (ratioOfNatSucc 4 (2 * (2 * baseIndex + 1) + 1)) :=
  denotesSameAsTrans
    (denotesSameAsSymm (reciprocalDoubleSumDenotesSame baseIndex))
    (denotesSameAsTrans
      (addExactRespectsDenotesSameAs
        (denotesSameAsSymm
          (reciprocalDoubleSumDenotesSame (2 * baseIndex + 1)))
        (denotesSameAsSymm
          (reciprocalDoubleSumDenotesSame (2 * baseIndex + 1))))
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (ratioOfNatSuccSumDenotesSame 1 1 (2 * (2 * baseIndex + 1) + 1))
          (ratioOfNatSuccSumDenotesSame 1 1 (2 * (2 * baseIndex + 1) + 1)))
        (ratioOfNatSuccSumDenotesSame 2 2 (2 * (2 * baseIndex + 1) + 1))))

end RationalPair

open RationalPair

/-- **The positivity witness**: an index whose approximant clears the
DOUBLED margin `2/(w+1)`.  `Type`-valued — the constructive order carries
data, and the inverse (R-5) computes from the index. -/
structure RealPositivityWitness (value : RegularReal) : Type where
  marginIndex : Nat
  hasDoubledMargin : LessEqualAs (ratioOfNatSucc 2 marginIndex)
    (value.approximation marginIndex)

/-- **The tail lemma**: the doubled margin at the witness forces the HALF
margin `1/(2w+2)` at every index past `2w+1` — regularity eats one
`1/(w+1)`, the depth bound eats at most another half, and the shared-addend
cancellation reads off the remainder. -/
theorem tailStaysAboveHalfMargin {value : RegularReal} {marginIndex : Nat}
    (hasDoubledMargin : LessEqualAs (ratioOfNatSucc 2 marginIndex)
      (value.approximation marginIndex))
    {tailIndex : Nat} (isDeep : 2 * marginIndex + 1 ≤ tailIndex) :
    LessEqualAs (reciprocalOfSucc (2 * marginIndex + 1))
      (value.approximation tailIndex) :=
  have shunted : LessEqualAs (value.approximation marginIndex)
      (addExact (value.approximation tailIndex)
        (addExact (reciprocalOfSucc marginIndex)
          (reciprocalOfSucc tailIndex))) :=
    lessEqualAsAddOfSubLessEqual (value.isRegular marginIndex tailIndex).left
  have chained : LessEqualAs (ratioOfNatSucc 2 marginIndex)
      (addExact (value.approximation tailIndex)
        (addExact (reciprocalOfSucc marginIndex)
          (reciprocalOfSucc (2 * marginIndex + 1)))) :=
    lessEqualAsTrans hasDoubledMargin
      (lessEqualAsTrans shunted
        (addExactMonotone (lessEqualAsRefl (value.approximation tailIndex))
          (addExactMonotone (lessEqualAsRefl (reciprocalOfSucc marginIndex))
            (ratioOfNatSuccAntitoneDenominator 1 isDeep))))
  have marginSplits : DenotesSameAs (ratioOfNatSucc 2 marginIndex)
      (addExact (reciprocalOfSucc (2 * marginIndex + 1))
        (addExact (reciprocalOfSucc marginIndex)
          (reciprocalOfSucc (2 * marginIndex + 1)))) :=
    denotesSameAsTrans
      (denotesSameAsSymm (ratioOfNatSuccSumDenotesSame 1 1 marginIndex))
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (denotesSameAsRefl (reciprocalOfSucc marginIndex))
          (denotesSameAsSymm (reciprocalDoubleSumDenotesSame marginIndex)))
        (denotesSameAsTrans
          (denotesSameAsSymm
            (addExactAssoc (reciprocalOfSucc marginIndex)
              (reciprocalOfSucc (2 * marginIndex + 1))
              (reciprocalOfSucc (2 * marginIndex + 1))))
          (addExactComm
            (addExact (reciprocalOfSucc marginIndex)
              (reciprocalOfSucc (2 * marginIndex + 1)))
            (reciprocalOfSucc (2 * marginIndex + 1)))))
  lessEqualAsAddRightCancel (lessEqualAsCongrLeft marginSplits chained)

/-- **Positivity transports along the setoid** — re-witness at the
twice-doubled tail index, where the half margin left by the tail lemma
splits EXACTLY into the setoid drift `2/(m+1)` plus the new doubled margin
`2/(m+1)`. -/
def realPositivityWitnessCongr {value newValue : RegularReal}
    (areSame : DenotesSameReal value newValue)
    (witness : RealPositivityWitness value) :
    RealPositivityWitness newValue :=
  let newMarginIndex := 2 * (2 * (2 * witness.marginIndex + 1) + 1) + 1
  { marginIndex := newMarginIndex
    hasDoubledMargin :=
      have isDeep : 2 * witness.marginIndex + 1 ≤ newMarginIndex :=
        natLeTrans (natSelfLeDoubleSelfSucc (2 * witness.marginIndex + 1))
          (natSelfLeDoubleSelfSucc (2 * (2 * witness.marginIndex + 1) + 1))
      have chained :
          LessEqualAs (reciprocalOfSucc (2 * witness.marginIndex + 1))
            (addExact (newValue.approximation newMarginIndex)
              (ratioOfNatSucc 2 newMarginIndex)) :=
        lessEqualAsTrans
          (tailStaysAboveHalfMargin witness.hasDoubledMargin isDeep)
          (lessEqualAsAddOfSubLessEqual (areSame newMarginIndex).left)
      have quadruples :
          DenotesSameAs (reciprocalOfSucc (2 * witness.marginIndex + 1))
            (addExact (ratioOfNatSucc 2 newMarginIndex)
              (ratioOfNatSucc 2 newMarginIndex)) :=
        denotesSameAsTrans
          (reciprocalQuadrupleSplitDenotesSame (2 * witness.marginIndex + 1))
          (denotesSameAsSymm
            (ratioOfNatSuccSumDenotesSame 2 2 newMarginIndex))
      lessEqualAsAddRightCancel (lessEqualAsCongrLeft quadruples chained) }

/-! ## The strict order and cotransitivity (NUM-R-4b)

`a < b` is a positivity witness on the difference; apartness is a sum of
strict orders.  COTRANSITIVITY replaces trichotomy: from `a < b`, any `c`
sits strictly above `a` or strictly below `b` — DECIDE the middle's
difference against half the tail margin at the nested-doubled index, where
the margin arithmetic is exact in both arms. -/

namespace RationalPair

/-- The reciprocal halves exactly: `1/(b+1)` denotes `2/(2b+2)` — one
doubling identity and one same-denominator sum. -/
theorem reciprocalHalvesDenotesSame (baseIndex : Nat) :
    DenotesSameAs (reciprocalOfSucc baseIndex)
      (ratioOfNatSucc 2 (2 * baseIndex + 1)) :=
  denotesSameAsTrans
    (denotesSameAsSymm (reciprocalDoubleSumDenotesSame baseIndex))
    (ratioOfNatSuccSumDenotesSame 1 1 (2 * baseIndex + 1))

/-- A refuted bound reverses — totality read off the refutation, weakened
back to the order. -/
theorem lessEqualAsOfNotLessEqual {leftValue rightValue : RationalPair}
    (isNotBelow : Not (LessEqualAs leftValue rightValue)) :
    LessEqualAs rightValue leftValue :=
  intLessEqualOfLessThan (intLessThanOfNotLessEqual isNotBelow)

end RationalPair

/-- Exact subtraction on reals — addition of the negation.  Its approximant
at `n` IS `subExact` of the factors sampled at `2n+1`, definitionally. -/
def subReal (leftValue rightValue : RegularReal) : RegularReal :=
  addReal leftValue (negReal rightValue)

/-- **The strict order**: `left < right` is a positivity witness on the
difference — `Type`-valued, carrying the margin index. -/
def LessThanReal (leftValue rightValue : RegularReal) : Type :=
  RealPositivityWitness (subReal rightValue leftValue)

/-- **Apartness**: a strict separation one way or the other. -/
def RealApartnessWitness (leftValue rightValue : RegularReal) : Type :=
  Sum (LessThanReal leftValue rightValue)
    (LessThanReal rightValue leftValue)

/-- Apartness is symmetric — swap the sum. -/
def realApartnessWitnessSymm {leftValue rightValue : RegularReal}
    (areApart : RealApartnessWitness leftValue rightValue) :
    RealApartnessWitness rightValue leftValue :=
  match areApart with
  | .inl isBelow => .inr isBelow
  | .inr isAbove => .inl isAbove

/-- **Cotransitivity** — the constructive replacement for trichotomy: from
`left < right`, every `middle` sits strictly above `left` or strictly below
`right`.  Decide the middle difference against HALF the tail margin at the
nested-doubled index: an affirmed half-margin IS the doubled margin there
(the halving identity); a refuted one leaves the other half to the right
difference through the subtraction chain, the shared-addend cancellation
reading it off. -/
def lessThanRealCotransitive {leftValue rightValue : RegularReal}
    (isBelow : LessThanReal leftValue rightValue)
    (middleValue : RegularReal) :
    Sum (LessThanReal leftValue middleValue)
      (LessThanReal middleValue rightValue) :=
  let baseIndex := 2 * isBelow.marginIndex + 1
  let decisionIndex := 2 * (2 * baseIndex + 1) + 1
  match decideLessEqualAs (reciprocalOfSucc (2 * baseIndex + 1))
      ((subReal middleValue leftValue).approximation decisionIndex) with
  | .isTrue hasGap =>
      Sum.inl
        { marginIndex := decisionIndex
          hasDoubledMargin :=
            lessEqualAsCongrLeft
              (reciprocalHalvesDenotesSame (2 * baseIndex + 1)) hasGap }
  | .isFalse lacksGap =>
      Sum.inr
        { marginIndex := decisionIndex
          hasDoubledMargin :=
            have isDeep : 2 * isBelow.marginIndex + 1 ≤ decisionIndex :=
              natLeTrans (natSelfLeDoubleSelfSucc baseIndex)
                (natSelfLeDoubleSelfSucc (2 * baseIndex + 1))
            have tailBound :
                LessEqualAs
                  (reciprocalOfSucc (2 * isBelow.marginIndex + 1))
                  ((subReal rightValue leftValue).approximation
                    decisionIndex) :=
              tailStaysAboveHalfMargin isBelow.hasDoubledMargin isDeep
            have splitTail :
                LessEqualAs
                  (addExact (reciprocalOfSucc (2 * baseIndex + 1))
                    (reciprocalOfSucc (2 * baseIndex + 1)))
                  ((subReal rightValue leftValue).approximation
                    decisionIndex) :=
              lessEqualAsCongrLeft
                (denotesSameAsSymm (reciprocalDoubleSumDenotesSame baseIndex))
                tailBound
            have chainedThroughMiddle :
                LessEqualAs
                  (addExact (reciprocalOfSucc (2 * baseIndex + 1))
                    (reciprocalOfSucc (2 * baseIndex + 1)))
                  (addExact
                    (subExact
                      (rightValue.approximation (2 * decisionIndex + 1))
                      (middleValue.approximation (2 * decisionIndex + 1)))
                    (subExact
                      (middleValue.approximation (2 * decisionIndex + 1))
                      (leftValue.approximation (2 * decisionIndex + 1)))) :=
              lessEqualAsCongrRight
                (denotesSameAsSymm
                  (subExactChainDenotesSame
                    (rightValue.approximation (2 * decisionIndex + 1))
                    (middleValue.approximation (2 * decisionIndex + 1))
                    (leftValue.approximation (2 * decisionIndex + 1))))
                splitTail
            have relaxedThroughMiddle :
                LessEqualAs
                  (addExact (reciprocalOfSucc (2 * baseIndex + 1))
                    (reciprocalOfSucc (2 * baseIndex + 1)))
                  (addExact
                    (subExact
                      (rightValue.approximation (2 * decisionIndex + 1))
                      (middleValue.approximation (2 * decisionIndex + 1)))
                    (reciprocalOfSucc (2 * baseIndex + 1))) :=
              lessEqualAsTrans chainedThroughMiddle
                (addExactMonotone
                  (lessEqualAsRefl
                    (subExact
                      (rightValue.approximation (2 * decisionIndex + 1))
                      (middleValue.approximation (2 * decisionIndex + 1))))
                  (lessEqualAsOfNotLessEqual lacksGap))
            lessEqualAsCongrLeft
              (reciprocalHalvesDenotesSame (2 * baseIndex + 1))
              (lessEqualAsAddRightCancel relaxedThroughMiddle) }

/-! ## Irreflexivity, congruence, additive compatibility (NUM-R-4c)

The remaining strict-order package: irreflexivity (the self-difference
denotes zero, refuting any margin), the setoid congruences (re-witness
through the subtraction congruence), the apartness corollaries, and
additive op-compatibility (the shared summand cancels EXACTLY pointwise,
so the witness transports through one tail step and one halving).

Deferred to R-5, where the Heyting-field work needs them: positivity
closure under `mulReal` (margin = product of margins at the scaled
index), and the `Prop`-valued non-strict order `LessEqualReal`. -/

namespace RationalPair

/-- **The shared addend cancels under subtraction** — exactly, as a setoid
identity: negation distributes into the subtrahend, the medial law
regroups the four summands, and the `s + (-s)` block collapses to zero. -/
theorem subExactSharedAddendCancelDenotesSame
    (highValue lowValue sharedValue : RationalPair) :
    DenotesSameAs
      (subExact (addExact highValue sharedValue)
        (addExact lowValue sharedValue))
      (subExact highValue lowValue) :=
  denotesSameAsTrans
    (addExactRespectsDenotesSameAs
      (denotesSameAsRefl (addExact highValue sharedValue))
      (negExactAddExactDenotesSame lowValue sharedValue))
    (denotesSameAsTrans
      (addExactMedialDenotesSame highValue sharedValue
        (negExact lowValue) (negExact sharedValue))
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (denotesSameAsRefl (subExact highValue lowValue))
          (addExactNegRight sharedValue))
        (addExactZeroRight (subExact highValue lowValue))))

end RationalPair

/-- Subtraction respects the real setoid — compose the addition and
negation congruences. -/
theorem subRealRespectsDenotesSame
    {leftValue newLeftValue rightValue newRightValue : RegularReal}
    (leftAgrees : DenotesSameReal leftValue newLeftValue)
    (rightAgrees : DenotesSameReal rightValue newRightValue) :
    DenotesSameReal (subReal leftValue rightValue)
      (subReal newLeftValue newRightValue) :=
  addRealRespectsDenotesSame leftAgrees
    (negRealRespectsDenotesSame rightAgrees)

/-- **Irreflexivity**: no value sits strictly below itself — the
self-difference approximant is `v − v`, which denotes zero, and a doubled
margin below zero collapses to `2 ≤ 0` on the numerators. -/
theorem lessThanRealIrrefl {value : RegularReal}
    (isBelowSelf : LessThanReal value value) : False :=
  have marginAtZero : LessEqualAs
      (ratioOfNatSucc 2 isBelowSelf.marginIndex) zeroRational :=
    lessEqualAsCongrRight
      (addExactNegRight
        (value.approximation (2 * isBelowSelf.marginIndex + 1)))
      isBelowSelf.hasDoubledMargin
  nomatch natLeOfIntOfNatLe (intLessEqualOfEqRight marginAtZero
    (intZeroMul (denominatorInt (ratioOfNatSucc 2 isBelowSelf.marginIndex))))

/-- Apartness is irreflexive — both arms refute through the strict
order's irreflexivity. -/
theorem realApartnessWitnessIrrefl {value : RegularReal}
    (isApartFromSelf : RealApartnessWitness value value) : False :=
  match isApartFromSelf with
  | .inl isBelowSelf => lessThanRealIrrefl isBelowSelf
  | .inr isAboveSelf => lessThanRealIrrefl isAboveSelf

/-- **The strict order respects the setoid** on both sides — the
difference congruence feeds the positivity transport. -/
def lessThanRealCongr
    {leftValue newLeftValue rightValue newRightValue : RegularReal}
    (leftAgrees : DenotesSameReal leftValue newLeftValue)
    (rightAgrees : DenotesSameReal rightValue newRightValue)
    (isBelow : LessThanReal leftValue rightValue) :
    LessThanReal newLeftValue newRightValue :=
  realPositivityWitnessCongr
    (subRealRespectsDenotesSame rightAgrees leftAgrees) isBelow

/-- Apartness respects the setoid — transport each arm. -/
def realApartnessWitnessCongr
    {leftValue newLeftValue rightValue newRightValue : RegularReal}
    (leftAgrees : DenotesSameReal leftValue newLeftValue)
    (rightAgrees : DenotesSameReal rightValue newRightValue)
    (areApart : RealApartnessWitness leftValue rightValue) :
    RealApartnessWitness newLeftValue newRightValue :=
  match areApart with
  | .inl isBelow => .inl (lessThanRealCongr leftAgrees rightAgrees isBelow)
  | .inr isAbove => .inr (lessThanRealCongr rightAgrees leftAgrees isAbove)

/-- Apartness is cotransitive — route each arm through the strict order's
cotransitivity and re-tag the sums. -/
def realApartnessWitnessCotransitive {leftValue rightValue : RegularReal}
    (areApart : RealApartnessWitness leftValue rightValue)
    (middleValue : RegularReal) :
    Sum (RealApartnessWitness leftValue middleValue)
      (RealApartnessWitness middleValue rightValue) :=
  match areApart with
  | .inl isBelow =>
      match lessThanRealCotransitive isBelow middleValue with
      | .inl isLeftBelowMiddle => .inl (.inl isLeftBelowMiddle)
      | .inr isMiddleBelowRight => .inr (.inl isMiddleBelowRight)
  | .inr isAbove =>
      match lessThanRealCotransitive isAbove middleValue with
      | .inl isRightBelowMiddle => .inr (.inr isRightBelowMiddle)
      | .inr isMiddleBelowLeft => .inl (.inr isMiddleBelowLeft)

/-- **Additive compatibility**: adding a shared value preserves the strict
order.  The shifted difference approximant cancels the shared summand
EXACTLY (pointwise setoid identity), landing on the original difference at
a deeper sample — one tail step recovers the half margin and the halving
identity re-reads it as the doubled margin at the new index. -/
def lessThanRealAddCompat {leftValue rightValue : RegularReal}
    (isBelow : LessThanReal leftValue rightValue)
    (sharedValue : RegularReal) :
    LessThanReal (addReal leftValue sharedValue)
      (addReal rightValue sharedValue) :=
  let compatIndex := 2 * (2 * isBelow.marginIndex + 1) + 1
  let sampleIndex := 2 * (2 * compatIndex + 1) + 1
  { marginIndex := compatIndex
    hasDoubledMargin :=
      have isDeep : 2 * isBelow.marginIndex + 1 ≤ 2 * compatIndex + 1 :=
        natLeTrans (natSelfLeDoubleSelfSucc (2 * isBelow.marginIndex + 1))
          (natSelfLeDoubleSelfSucc compatIndex)
      have reshapedMargin : LessEqualAs (ratioOfNatSucc 2 compatIndex)
          ((subReal rightValue leftValue).approximation
            (2 * compatIndex + 1)) :=
        lessEqualAsCongrLeft
          (reciprocalHalvesDenotesSame (2 * isBelow.marginIndex + 1))
          (tailStaysAboveHalfMargin isBelow.hasDoubledMargin isDeep)
      lessEqualAsCongrRight
        (denotesSameAsSymm
          (subExactSharedAddendCancelDenotesSame
            (rightValue.approximation sampleIndex)
            (leftValue.approximation sampleIndex)
            (sharedValue.approximation sampleIndex)))
        reshapedMargin }

/-- Apartness is compatible with a shared addition — transport each arm. -/
def realApartnessWitnessAddCompat {leftValue rightValue : RegularReal}
    (areApart : RealApartnessWitness leftValue rightValue)
    (sharedValue : RegularReal) :
    RealApartnessWitness (addReal leftValue sharedValue)
      (addReal rightValue sharedValue) :=
  match areApart with
  | .inl isBelow => .inl (lessThanRealAddCompat isBelow sharedValue)
  | .inr isAbove => .inr (lessThanRealAddCompat isAbove sharedValue)

/-- **Transitivity**: chain two margins through the middle.  At the SUMMED
index both tail lemmas fire; the chain identity glues the two differences
exactly at the shared sample, and the two reciprocals — each relaxed to the
summed index by antitonicity — recombine to the doubled margin there.  No
estimates, no new ℚ facts. -/
def lessThanRealTrans {leftValue middleValue rightValue : RegularReal}
    (isBelowMiddle : LessThanReal leftValue middleValue)
    (isMiddleBelow : LessThanReal middleValue rightValue) :
    LessThanReal leftValue rightValue :=
  let lowerTailIndex := 2 * isBelowMiddle.marginIndex + 1
  let upperTailIndex := 2 * isMiddleBelow.marginIndex + 1
  let transIndex := lowerTailIndex + upperTailIndex
  { marginIndex := transIndex
    hasDoubledMargin :=
      have lowerTail : LessEqualAs (reciprocalOfSucc lowerTailIndex)
          ((subReal middleValue leftValue).approximation transIndex) :=
        tailStaysAboveHalfMargin isBelowMiddle.hasDoubledMargin
          (Nat.le_add_right lowerTailIndex upperTailIndex)
      have upperTail : LessEqualAs (reciprocalOfSucc upperTailIndex)
          ((subReal rightValue middleValue).approximation transIndex) :=
        tailStaysAboveHalfMargin isMiddleBelow.hasDoubledMargin
          (Nat.le_add_left upperTailIndex lowerTailIndex)
      have summedTails : LessEqualAs
          (addExact (reciprocalOfSucc transIndex)
            (reciprocalOfSucc transIndex))
          (addExact
            ((subReal rightValue middleValue).approximation transIndex)
            ((subReal middleValue leftValue).approximation transIndex)) :=
        lessEqualAsTrans
          (addExactMonotone
            (ratioOfNatSuccAntitoneDenominator 1
              (Nat.le_add_left upperTailIndex lowerTailIndex))
            (ratioOfNatSuccAntitoneDenominator 1
              (Nat.le_add_right lowerTailIndex upperTailIndex)))
          (addExactMonotone upperTail lowerTail)
      lessEqualAsCongrLeft (ratioOfNatSuccSumDenotesSame 1 1 transIndex)
        (lessEqualAsCongrRight
          (subExactChainDenotesSame
            (rightValue.approximation (2 * transIndex + 1))
            (middleValue.approximation (2 * transIndex + 1))
            (leftValue.approximation (2 * transIndex + 1)))
          summedTails) }

/-- **Asymmetry** — two opposite strict orders chain to a self-order,
refuted by irreflexivity. -/
theorem lessThanRealAsymm {leftValue rightValue : RegularReal}
    (isBelow : LessThanReal leftValue rightValue)
    (isAbove : LessThanReal rightValue leftValue) : False :=
  lessThanRealIrrefl (lessThanRealTrans isBelow isAbove)

end FX1Poly.ComputerAlgebra
