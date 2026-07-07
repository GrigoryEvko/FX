import FX1Poly.ComputerAlgebra.Number.RegularRealInverse

/-! # RegularReal commutative-ring laws (NUM-R-4)

The ℝ-level ring axioms on `RegularReal`, the substrate the ℂ = (re, im)
lift consumes.  The arithmetic operations (`addReal`, `negReal`, `subReal`,
`mulReal`) and their setoid congruences ship in the R-2/R-3 files; here we
prove the LAWS those operations satisfy up to `DenotesSameReal`.

Three sampling geometries govern the difficulty:

* **Pointwise** — both sides sample every atom at the SAME index, so the law
  is a per-index ℚ setoid identity carried through `isWithinBoundCongr*` on a
  reflexive self-bound.  Commutativity of `+`, the additive inverse, and the
  two negation-passing bricks (`negRealNegReal`, `negRealAddReal`) are all of
  this kind — no analysis beyond the shipped `*Exact` ℚ law.

* **One-sided sampling shift** — one side samples an atom at `2n+1` (or the
  bound-scaled deep index) while the comparison target samples it at `n`.
  Regularity bridges the drift, and because the deep index dominates `n` the
  drift already sits below the `2/(n+1)` setoid modulus — no slack closure.
  The identities and the zero laws are of this kind.

* **Commutation-of-scale** — the two products sample at bound-scaled indices
  that differ only by a `Nat.add_comm` in the shared-bound numerator, hence
  are propositionally EQUAL; an explicit-motive `Eq.rec` collapses the
  mismatch to the pointwise case.  `mulReal` commutativity is of this kind.

Associativity of `+`, and associativity/distributivity of `·`, sample atoms
at genuinely distinct depths on the two sides and are the real slack-closure
bricks — they live further down in this file (or are flagged open). -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## The deep-sample drift bridge

The one-sided-shift workhorse: an approximant sampled at any index dominating
`shallowIndex` sits within the `2/(shallow+1)` setoid modulus of the
approximant at `shallowIndex` — regularity against the pair, the deep
reciprocal relaxed by antitonicity, the halves recombined.  Generalizes the
`2n+1`-vs-`n` special case (`doubledSampleDriftIsWithinSetoidBound`). -/

/-- Any deep sample sits within the setoid modulus of the shallow sample. -/
theorem deepSampleDriftIsWithinSetoidBound (value : RegularReal)
    {shallowIndex deepIndex : Nat} (isDeep : shallowIndex ≤ deepIndex) :
    IsWithinBound (value.approximation deepIndex)
      (value.approximation shallowIndex) (ratioOfNatSucc 2 shallowIndex) :=
  isWithinBoundCongrBound (ratioOfNatSuccSumDenotesSame 1 1 shallowIndex)
    (isWithinBoundOfBoundLessEqual
      (addExactMonotone
        (ratioOfNatSuccAntitoneDenominator 1 isDeep)
        (lessEqualAsRefl (reciprocalOfSucc shallowIndex)))
      (value.isRegular deepIndex shallowIndex))

/-! ## Negation-passing bricks (pointwise) -/

/-- Double negation on reals denotes the value back — pointwise, from the ℚ
numerator round-trip. -/
theorem negRealNegRealDenotesSame (value : RegularReal) :
    DenotesSameReal (negReal (negReal value)) value :=
  fun sharedIndex =>
    isWithinBoundCongrLeft
      (denotesSameAsSymm
        (negExactNegExactDenotesSame (value.approximation sharedIndex)))
      (isWithinBoundSelfOfNonNegative (ratioOfNatSuccIsNonNegative 2 sharedIndex))

/-- Negation distributes over addition on reals — pointwise, both sides
sample at `2n+1` and the ℚ identity is `negExactAddExact`. -/
theorem negRealAddRealDenotesSame (leftValue rightValue : RegularReal) :
    DenotesSameReal (negReal (addReal leftValue rightValue))
      (addReal (negReal leftValue) (negReal rightValue)) :=
  fun sharedIndex =>
    isWithinBoundCongrLeft
      (denotesSameAsSymm
        (negExactAddExactDenotesSame
          (leftValue.approximation (2 * sharedIndex + 1))
          (rightValue.approximation (2 * sharedIndex + 1))))
      (isWithinBoundSelfOfNonNegative (ratioOfNatSuccIsNonNegative 2 sharedIndex))

/-! ## Additive-group laws -/

/-- **Addition is commutative** — pointwise, both sides sample at `2n+1`. -/
theorem addRealComm (leftValue rightValue : RegularReal) :
    DenotesSameReal (addReal leftValue rightValue)
      (addReal rightValue leftValue) :=
  fun sharedIndex =>
    isWithinBoundCongrRight
      (addExactComm (leftValue.approximation (2 * sharedIndex + 1))
        (rightValue.approximation (2 * sharedIndex + 1)))
      (isWithinBoundSelfOfNonNegative (ratioOfNatSuccIsNonNegative 2 sharedIndex))

/-- **Zero is a right identity** for addition — the zero addend collapses and
the `2n+1`-vs-`n` drift is absorbed by the value's regularity. -/
theorem addRealZeroRight (value : RegularReal) :
    DenotesSameReal (addReal value (constantReal zeroRational)) value :=
  fun sharedIndex =>
    isWithinBoundCongrLeft
      (denotesSameAsSymm
        (addExactZeroRight (value.approximation (2 * sharedIndex + 1))))
      (doubledSampleDriftIsWithinSetoidBound value sharedIndex)

/-- **Zero is a left identity** for addition. -/
theorem addRealZeroLeft (value : RegularReal) :
    DenotesSameReal (addReal (constantReal zeroRational) value) value :=
  fun sharedIndex =>
    isWithinBoundCongrLeft
      (denotesSameAsSymm
        (addExactZeroLeft (value.approximation (2 * sharedIndex + 1))))
      (doubledSampleDriftIsWithinSetoidBound value sharedIndex)

/-- **Negation is a right inverse** for addition — pointwise, the ℚ
cancellation `v + (-v)` denotes zero at the shared `2n+1` sample. -/
theorem addRealNegRight (value : RegularReal) :
    DenotesSameReal (addReal value (negReal value)) (constantReal zeroRational) :=
  fun sharedIndex =>
    isWithinBoundCongrLeft
      (denotesSameAsSymm
        (addExactNegRight (value.approximation (2 * sharedIndex + 1))))
      (isWithinBoundSelfOfNonNegative (ratioOfNatSuccIsNonNegative 2 sharedIndex))

/-! ## Multiplicative laws (identity, commutativity, zero) -/

/-- The product against constant zero vanishes at ℚ — `v · 0` denotes 0. -/
theorem mulExactZeroRightDenotesSame (value : RationalPair) :
    DenotesSameAs (mulExact value zeroRational) zeroRational :=
  have numeratorVanishes : (mulExact value zeroRational).numerator = 0 :=
    intMulZero value.numerator
  (congrArg (· * denominatorInt zeroRational) numeratorVanishes).trans
    ((intZeroMul (denominatorInt zeroRational)).trans
      (intZeroMul (denominatorInt (mulExact value zeroRational))).symm)

/-- The product against constant zero on the left vanishes at ℚ. -/
theorem mulExactZeroLeftDenotesSame (value : RationalPair) :
    DenotesSameAs (mulExact zeroRational value) zeroRational :=
  denotesSameAsTrans (mulExactComm zeroRational value)
    (mulExactZeroRightDenotesSame value)

/-- **One is a right identity** for multiplication — the unit factor collapses
and the deep bound-scaled sample sits within the setoid modulus. -/
theorem mulRealOneRight (value : RegularReal) :
    DenotesSameReal (mulReal value (constantReal oneRational)) value :=
  fun sharedIndex =>
    isWithinBoundCongrLeft
      (denotesSameAsSymm
        (mulExactOneRight
          (value.approximation
            (productSamplingIndex value (constantReal oneRational) sharedIndex))))
      (deepSampleDriftIsWithinSetoidBound value
        (natSelfLeBoundScaledIndex
          (sharedBoundNumeratorPredecessor value (constantReal oneRational))
          sharedIndex))

/-- **One is a left identity** for multiplication. -/
theorem mulRealOneLeft (value : RegularReal) :
    DenotesSameReal (mulReal (constantReal oneRational) value) value :=
  fun sharedIndex =>
    isWithinBoundCongrLeft
      (denotesSameAsSymm
        (mulExactOneLeft
          (value.approximation
            (productSamplingIndex (constantReal oneRational) value sharedIndex))))
      (deepSampleDriftIsWithinSetoidBound value
        (natSelfLeBoundScaledIndex
          (sharedBoundNumeratorPredecessor (constantReal oneRational) value)
          sharedIndex))

/-- **Product against constant zero denotes zero** — pointwise, the ℚ
zero-product identity at the deep sample. -/
theorem mulRealZeroRight (value : RegularReal) :
    DenotesSameReal (mulReal value (constantReal zeroRational))
      (constantReal zeroRational) :=
  fun sharedIndex =>
    isWithinBoundCongrLeft
      (denotesSameAsSymm
        (mulExactZeroRightDenotesSame
          (value.approximation
            (productSamplingIndex value (constantReal zeroRational) sharedIndex))))
      (isWithinBoundSelfOfNonNegative (ratioOfNatSuccIsNonNegative 2 sharedIndex))

/-- **Constant zero against a product denotes zero**. -/
theorem mulRealZeroLeft (value : RegularReal) :
    DenotesSameReal (mulReal (constantReal zeroRational) value)
      (constantReal zeroRational) :=
  fun sharedIndex =>
    isWithinBoundCongrLeft
      (denotesSameAsSymm
        (mulExactZeroLeftDenotesSame
          (value.approximation
            (productSamplingIndex (constantReal zeroRational) value sharedIndex))))
      (isWithinBoundSelfOfNonNegative (ratioOfNatSuccIsNonNegative 2 sharedIndex))

/-- **Multiplication is commutative** — the two products sample at
bound-scaled indices differing only by `Nat.add_comm` in the shared-bound
numerator; those indices are propositionally equal, so an explicit-motive
`Eq.rec` reduces the goal to the pointwise `mulExactComm` case. -/
theorem mulRealComm (leftValue rightValue : RegularReal) :
    DenotesSameReal (mulReal leftValue rightValue)
      (mulReal rightValue leftValue) :=
  fun sharedIndex =>
    have indexesAgree :
        productSamplingIndex rightValue leftValue sharedIndex =
          productSamplingIndex leftValue rightValue sharedIndex :=
      congrArg (fun boundNumerator => boundScaledIndex boundNumerator sharedIndex)
        (Nat.add_comm (canonicalBoundNumerator rightValue)
          (canonicalBoundNumerator leftValue))
    have atSharedSample :
        IsWithinBound
          (mulExact
            (leftValue.approximation
              (productSamplingIndex leftValue rightValue sharedIndex))
            (rightValue.approximation
              (productSamplingIndex leftValue rightValue sharedIndex)))
          (mulExact
            (rightValue.approximation
              (productSamplingIndex leftValue rightValue sharedIndex))
            (leftValue.approximation
              (productSamplingIndex leftValue rightValue sharedIndex)))
          (ratioOfNatSucc 2 sharedIndex) :=
      isWithinBoundCongrRight
        (mulExactComm
          (leftValue.approximation
            (productSamplingIndex leftValue rightValue sharedIndex))
          (rightValue.approximation
            (productSamplingIndex leftValue rightValue sharedIndex)))
        (isWithinBoundSelfOfNonNegative
          (ratioOfNatSuccIsNonNegative 2 sharedIndex))
    Eq.rec
      (motive := fun sampledIndex _ =>
        IsWithinBound
          (mulExact
            (leftValue.approximation
              (productSamplingIndex leftValue rightValue sharedIndex))
            (rightValue.approximation
              (productSamplingIndex leftValue rightValue sharedIndex)))
          (mulExact (rightValue.approximation sampledIndex)
            (leftValue.approximation sampledIndex))
          (ratioOfNatSucc 2 sharedIndex))
      atSharedSample indexesAgree.symm

/-! ## Additive associativity (slack closure)

`(a + b) + c` and `a + (b + c)` sample their atoms at genuinely DIFFERENT
depths: the outer summand is double-sampled at `2s+1` while the inner pair is
quadruple-sampled at `2(2s+1)+1`, and the roles of `a` and `c` swap between
the two groupings.  So the law is not pointwise — it goes through slack
closure.  At each shared index, chain both sides to a slack index by their
own regularity; there, associate the ℚ triple and bridge the two mismatched
atoms (`a` deep-vs-shallow, `c` shallow-vs-deep) by regularity, relaxing every
mismatch reciprocal to `1/(s+1)`; the accumulated bound reshapes onto
`2/(n+1)` plus a vanishing `7/(s+1)` slack, which closes. -/

/-- The five mismatch reciprocals of the associativity compare-bound collapse
onto `5/(s+1)` — three same-denominator sums. -/
theorem addRealAssocCompareBoundCollapses (slackIndex : Nat) :
    DenotesSameAs
      (addExact (addExact (reciprocalOfSucc slackIndex) (reciprocalOfSucc slackIndex))
        (addExact (reciprocalOfSucc slackIndex)
          (addExact (reciprocalOfSucc slackIndex) (reciprocalOfSucc slackIndex))))
      (ratioOfNatSucc 5 slackIndex) :=
  denotesSameAsTrans
    (addExactRespectsDenotesSameAs
      (ratioOfNatSuccSumDenotesSame 1 1 slackIndex)
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (denotesSameAsRefl (reciprocalOfSucc slackIndex))
          (ratioOfNatSuccSumDenotesSame 1 1 slackIndex))
        (ratioOfNatSuccSumDenotesSame 1 2 slackIndex)))
    (ratioOfNatSuccSumDenotesSame 2 3 slackIndex)

/-- **Addition is associative** up to the real setoid. -/
theorem addRealAssoc (firstValue middleValue lastValue : RegularReal) :
    DenotesSameReal
      (addReal (addReal firstValue middleValue) lastValue)
      (addReal firstValue (addReal middleValue lastValue)) :=
  fun sharedIndex =>
    isWithinBoundOfForallSlack (fun slackIndex =>
      have shallowIsBelowDeep :
          slackIndex ≤ 2 * (2 * slackIndex + 1) + 1 :=
        natLeTrans (natSelfLeDoubleSelfSucc slackIndex)
          (natSelfLeDoubleSelfSucc (2 * slackIndex + 1))
      have shallowIsBelowMid : slackIndex ≤ 2 * slackIndex + 1 :=
        natSelfLeDoubleSelfSucc slackIndex
      have deepReciprocalRelaxes :
          LessEqualAs (reciprocalOfSucc (2 * (2 * slackIndex + 1) + 1))
            (reciprocalOfSucc slackIndex) :=
        ratioOfNatSuccAntitoneDenominator 1 shallowIsBelowDeep
      have midReciprocalRelaxes :
          LessEqualAs (reciprocalOfSucc (2 * slackIndex + 1))
            (reciprocalOfSucc slackIndex) :=
        ratioOfNatSuccAntitoneDenominator 1 shallowIsBelowMid
      have compareBoundRelaxes :
          LessEqualAs
            (addExact
              (addExact
                (reciprocalOfSucc (2 * (2 * slackIndex + 1) + 1))
                (reciprocalOfSucc (2 * slackIndex + 1)))
              (addExact (reciprocalOfSucc (2 * slackIndex + 1))
                (addExact (reciprocalOfSucc (2 * slackIndex + 1))
                  (reciprocalOfSucc (2 * (2 * slackIndex + 1) + 1)))))
            (ratioOfNatSucc 5 slackIndex) :=
        lessEqualAsCongrRight (addRealAssocCompareBoundCollapses slackIndex)
          (addExactMonotone
            (addExactMonotone deepReciprocalRelaxes midReciprocalRelaxes)
            (addExactMonotone midReciprocalRelaxes
              (addExactMonotone midReciprocalRelaxes deepReciprocalRelaxes)))
      have compareInner :
          IsWithinBound
            (addExact
              (firstValue.approximation (2 * (2 * slackIndex + 1) + 1))
              (addExact
                (middleValue.approximation (2 * (2 * slackIndex + 1) + 1))
                (lastValue.approximation (2 * slackIndex + 1))))
            (addExact (firstValue.approximation (2 * slackIndex + 1))
              (addExact
                (middleValue.approximation (2 * (2 * slackIndex + 1) + 1))
                (lastValue.approximation (2 * (2 * slackIndex + 1) + 1))))
            (addExact
              (addExact
                (reciprocalOfSucc (2 * (2 * slackIndex + 1) + 1))
                (reciprocalOfSucc (2 * slackIndex + 1)))
              (addExact (reciprocalOfSucc (2 * slackIndex + 1))
                (addExact (reciprocalOfSucc (2 * slackIndex + 1))
                  (reciprocalOfSucc (2 * (2 * slackIndex + 1) + 1))))) :=
        addExactRespectsIsWithinBound
          (firstValue.isRegular (2 * (2 * slackIndex + 1) + 1)
            (2 * slackIndex + 1))
          (addExactRespectsIsWithinBound
            (isWithinBoundSelfOfNonNegative
              (ratioOfNatSuccIsNonNegative 1 (2 * slackIndex + 1)))
            (lastValue.isRegular (2 * slackIndex + 1)
              (2 * (2 * slackIndex + 1) + 1)))
      have compareAtSlack :
          IsWithinBound
            ((addReal (addReal firstValue middleValue) lastValue).approximation
              slackIndex)
            ((addReal firstValue (addReal middleValue lastValue)).approximation
              slackIndex)
            (ratioOfNatSucc 5 slackIndex) :=
        isWithinBoundOfBoundLessEqual compareBoundRelaxes
          (isWithinBoundCongrLeft
            (denotesSameAsSymm
              (addExactAssoc
                (firstValue.approximation (2 * (2 * slackIndex + 1) + 1))
                (middleValue.approximation (2 * (2 * slackIndex + 1) + 1))
                (lastValue.approximation (2 * slackIndex + 1))))
            compareInner)
      isWithinBoundCongrBound
        (denotesSameAsTrans
          (chainedSlackBoundReshapesDenotesSame (reciprocalOfSucc sharedIndex)
            (reciprocalOfSucc slackIndex) (ratioOfNatSucc 5 slackIndex))
          (addExactRespectsDenotesSameAs
            (ratioOfNatSuccSumDenotesSame 1 1 sharedIndex)
            (denotesSameAsTrans
              (addExactRespectsDenotesSameAs
                (ratioOfNatSuccSumDenotesSame 1 1 slackIndex)
                (denotesSameAsRefl (ratioOfNatSucc 5 slackIndex)))
              (ratioOfNatSuccSumDenotesSame 2 5 slackIndex))))
        (isWithinBoundTriangle
          (isWithinBoundTriangle
            ((addReal (addReal firstValue middleValue) lastValue).isRegular
              sharedIndex slackIndex)
            compareAtSlack)
          ((addReal firstValue (addReal middleValue lastValue)).isRegular
            slackIndex sharedIndex)))

/-! ## Multiplicative associativity and distributivity (slack closure)

`(x·y)·z` and `x·(y·z)` sample their three atoms at genuinely distinct
bound-scaled depths on the two sides — `x` at the left-inner vs the
right-outer index, `y` at the left-inner vs the right-inner, `z` at the
left-outer vs the right-inner — so the law is not pointwise.  At each shared
index it goes through slack closure: chain both products to a slack index by
their own regularity; there, reassociate the ℚ triple (`mulExactAssoc`) and
telescope through three product-difference legs (each one factor moving, the
other two held as magnitude-bounded multipliers) bridging the sampling
mismatch by regularity; every mismatch reciprocal relaxes to `2/(s+1)` and
each leg's constant magnitude collapses the accumulated bound onto a single
`K/(s+1)`, which reshapes onto `2/(n+1)` plus vanishing slack. -/

/-- Two deep samples sit within the doubled shallow modulus: the reciprocal
sum of any two indices dominating `shallowIndex` is below `2/(shallow+1)`. -/
theorem sumReciprocalBelowDoubleShallow {shallowIndex firstIndex secondIndex : Nat}
    (firstIsDeep : shallowIndex ≤ firstIndex)
    (secondIsDeep : shallowIndex ≤ secondIndex) :
    LessEqualAs
      (addExact (reciprocalOfSucc firstIndex) (reciprocalOfSucc secondIndex))
      (ratioOfNatSucc 2 shallowIndex) :=
  lessEqualAsCongrRight (ratioOfNatSuccSumDenotesSame 1 1 shallowIndex)
    (addExactMonotone
      (ratioOfNatSuccAntitoneDenominator 1 firstIsDeep)
      (ratioOfNatSuccAntitoneDenominator 1 secondIsDeep))

/-- **Multiplication is associative** up to the real setoid. -/
theorem mulRealAssoc (firstFactor secondFactor thirdFactor : RegularReal) :
    DenotesSameReal
      (mulReal (mulReal firstFactor secondFactor) thirdFactor)
      (mulReal firstFactor (mulReal secondFactor thirdFactor)) :=
  fun sharedIndex =>
    isWithinBoundOfForallSlack (fun slackIndex =>
      let leftOuterIndex :=
        productSamplingIndex (mulReal firstFactor secondFactor) thirdFactor
          slackIndex
      let leftInnerIndex :=
        productSamplingIndex firstFactor secondFactor leftOuterIndex
      let rightOuterIndex :=
        productSamplingIndex firstFactor (mulReal secondFactor thirdFactor)
          slackIndex
      let rightInnerIndex :=
        productSamplingIndex secondFactor thirdFactor rightOuterIndex
      let firstShiftNumerator :=
        canonicalBoundNumerator secondFactor * canonicalBoundNumerator thirdFactor
          * 2
      let secondShiftNumerator :=
        canonicalBoundNumerator firstFactor *
          (canonicalBoundNumerator thirdFactor * 2)
      let thirdShiftNumerator :=
        canonicalBoundNumerator firstFactor *
          (canonicalBoundNumerator secondFactor * 2)
      let middleNumerator :=
        firstShiftNumerator + secondShiftNumerator + thirdShiftNumerator
      have leftOuterIsDeep : slackIndex ≤ leftOuterIndex :=
        natSelfLeBoundScaledIndex
          (sharedBoundNumeratorPredecessor (mulReal firstFactor secondFactor)
            thirdFactor)
          slackIndex
      have leftInnerIsDeep : slackIndex ≤ leftInnerIndex :=
        natLeTrans leftOuterIsDeep
          (natSelfLeBoundScaledIndex
            (sharedBoundNumeratorPredecessor firstFactor secondFactor)
            leftOuterIndex)
      have rightOuterIsDeep : slackIndex ≤ rightOuterIndex :=
        natSelfLeBoundScaledIndex
          (sharedBoundNumeratorPredecessor firstFactor
            (mulReal secondFactor thirdFactor))
          slackIndex
      have rightInnerIsDeep : slackIndex ≤ rightInnerIndex :=
        natLeTrans rightOuterIsDeep
          (natSelfLeBoundScaledIndex
            (sharedBoundNumeratorPredecessor secondFactor thirdFactor)
            rightOuterIndex)
      have relaxedFirstDiff :
          IsWithinBound (firstFactor.approximation leftInnerIndex)
            (firstFactor.approximation rightOuterIndex)
            (ratioOfNatSucc 2 slackIndex) :=
        isWithinBoundOfBoundLessEqual
          (sumReciprocalBelowDoubleShallow leftInnerIsDeep rightOuterIsDeep)
          (firstFactor.isRegular leftInnerIndex rightOuterIndex)
      have relaxedSecondDiff :
          IsWithinBound (secondFactor.approximation leftInnerIndex)
            (secondFactor.approximation rightInnerIndex)
            (ratioOfNatSucc 2 slackIndex) :=
        isWithinBoundOfBoundLessEqual
          (sumReciprocalBelowDoubleShallow leftInnerIsDeep rightInnerIsDeep)
          (secondFactor.isRegular leftInnerIndex rightInnerIndex)
      have relaxedThirdDiff :
          IsWithinBound (thirdFactor.approximation leftOuterIndex)
            (thirdFactor.approximation rightInnerIndex)
            (ratioOfNatSucc 2 slackIndex) :=
        isWithinBoundOfBoundLessEqual
          (sumReciprocalBelowDoubleShallow leftOuterIsDeep rightInnerIsDeep)
          (thirdFactor.isRegular leftOuterIndex rightInnerIndex)
      have firstShiftLeg :
          IsWithinBound
            (mulExact (firstFactor.approximation leftInnerIndex)
              (mulExact (secondFactor.approximation leftInnerIndex)
                (thirdFactor.approximation leftOuterIndex)))
            (mulExact (firstFactor.approximation rightOuterIndex)
              (mulExact (secondFactor.approximation leftInnerIndex)
                (thirdFactor.approximation leftOuterIndex)))
            (mulExact
              (mulExact (canonicalBound secondFactor) (canonicalBound thirdFactor))
              (ratioOfNatSucc 2 slackIndex)) :=
        mulExactRespectsIsWithinBoundRight
          (isMagnitudeWithinMulExact
            (approximationIsWithinCanonicalBound secondFactor leftInnerIndex)
            (approximationIsWithinCanonicalBound thirdFactor leftOuterIndex)
            (canonicalBoundIsNonNegative thirdFactor))
          relaxedFirstDiff
          (ratioOfNatSuccIsNonNegative 2 slackIndex)
      have secondShiftLeg :
          IsWithinBound
            (mulExact (firstFactor.approximation rightOuterIndex)
              (mulExact (secondFactor.approximation leftInnerIndex)
                (thirdFactor.approximation leftOuterIndex)))
            (mulExact (firstFactor.approximation rightOuterIndex)
              (mulExact (secondFactor.approximation rightInnerIndex)
                (thirdFactor.approximation leftOuterIndex)))
            (mulExact (canonicalBound firstFactor)
              (mulExact (canonicalBound thirdFactor)
                (ratioOfNatSucc 2 slackIndex))) :=
        mulExactRespectsIsWithinBoundLeft
          (approximationIsWithinCanonicalBound firstFactor rightOuterIndex)
          (mulExactRespectsIsWithinBoundRight
            (approximationIsWithinCanonicalBound thirdFactor leftOuterIndex)
            relaxedSecondDiff
            (ratioOfNatSuccIsNonNegative 2 slackIndex))
          (mulExactIsNonNegative (canonicalBoundIsNonNegative thirdFactor)
            (ratioOfNatSuccIsNonNegative 2 slackIndex))
      have thirdShiftLeg :
          IsWithinBound
            (mulExact (firstFactor.approximation rightOuterIndex)
              (mulExact (secondFactor.approximation rightInnerIndex)
                (thirdFactor.approximation leftOuterIndex)))
            (mulExact (firstFactor.approximation rightOuterIndex)
              (mulExact (secondFactor.approximation rightInnerIndex)
                (thirdFactor.approximation rightInnerIndex)))
            (mulExact (canonicalBound firstFactor)
              (mulExact (canonicalBound secondFactor)
                (ratioOfNatSucc 2 slackIndex))) :=
        mulExactRespectsIsWithinBoundLeft
          (approximationIsWithinCanonicalBound firstFactor rightOuterIndex)
          (mulExactRespectsIsWithinBoundLeft
            (approximationIsWithinCanonicalBound secondFactor rightInnerIndex)
            relaxedThirdDiff
            (ratioOfNatSuccIsNonNegative 2 slackIndex))
          (mulExactIsNonNegative (canonicalBoundIsNonNegative secondFactor)
            (ratioOfNatSuccIsNonNegative 2 slackIndex))
      have middleBoundCollapses :
          DenotesSameAs
            (addExact
              (addExact
                (mulExact
                  (mulExact (canonicalBound secondFactor)
                    (canonicalBound thirdFactor))
                  (ratioOfNatSucc 2 slackIndex))
                (mulExact (canonicalBound firstFactor)
                  (mulExact (canonicalBound thirdFactor)
                    (ratioOfNatSucc 2 slackIndex))))
              (mulExact (canonicalBound firstFactor)
                (mulExact (canonicalBound secondFactor)
                  (ratioOfNatSucc 2 slackIndex))))
            (ratioOfNatSucc middleNumerator slackIndex) :=
        denotesSameAsTrans
          (addExactRespectsDenotesSameAs
            (addExactRespectsDenotesSameAs
              (denotesSameAsTrans
                (mulExactRespectsDenotesSameAs
                  (mulExactRatioRatioDenotesSame
                    (canonicalBoundNumerator secondFactor)
                    (canonicalBoundNumerator thirdFactor) 0)
                  (denotesSameAsRefl (ratioOfNatSucc 2 slackIndex)))
                (mulExactRatioRatioDenotesSame
                  (canonicalBoundNumerator secondFactor *
                    canonicalBoundNumerator thirdFactor)
                  2 slackIndex))
              (denotesSameAsTrans
                (mulExactRespectsDenotesSameAs
                  (denotesSameAsRefl (canonicalBound firstFactor))
                  (mulExactRatioRatioDenotesSame
                    (canonicalBoundNumerator thirdFactor) 2 slackIndex))
                (mulExactRatioRatioDenotesSame
                  (canonicalBoundNumerator firstFactor)
                  (canonicalBoundNumerator thirdFactor * 2) slackIndex)))
            (denotesSameAsTrans
              (mulExactRespectsDenotesSameAs
                (denotesSameAsRefl (canonicalBound firstFactor))
                (mulExactRatioRatioDenotesSame
                  (canonicalBoundNumerator secondFactor) 2 slackIndex))
              (mulExactRatioRatioDenotesSame
                (canonicalBoundNumerator firstFactor)
                (canonicalBoundNumerator secondFactor * 2) slackIndex)))
          (denotesSameAsTrans
            (addExactRespectsDenotesSameAs
              (ratioOfNatSuccSumDenotesSame firstShiftNumerator
                secondShiftNumerator slackIndex)
              (denotesSameAsRefl (ratioOfNatSucc thirdShiftNumerator slackIndex)))
            (ratioOfNatSuccSumDenotesSame
              (firstShiftNumerator + secondShiftNumerator) thirdShiftNumerator
              slackIndex))
      have compareAtSlack :
          IsWithinBound
            ((mulReal (mulReal firstFactor secondFactor) thirdFactor).approximation
              slackIndex)
            ((mulReal firstFactor (mulReal secondFactor thirdFactor)).approximation
              slackIndex)
            (addExact
              (addExact
                (mulExact
                  (mulExact (canonicalBound secondFactor)
                    (canonicalBound thirdFactor))
                  (ratioOfNatSucc 2 slackIndex))
                (mulExact (canonicalBound firstFactor)
                  (mulExact (canonicalBound thirdFactor)
                    (ratioOfNatSucc 2 slackIndex))))
              (mulExact (canonicalBound firstFactor)
                (mulExact (canonicalBound secondFactor)
                  (ratioOfNatSucc 2 slackIndex)))) :=
        isWithinBoundCongrLeft
          (denotesSameAsSymm
            (mulExactAssoc (firstFactor.approximation leftInnerIndex)
              (secondFactor.approximation leftInnerIndex)
              (thirdFactor.approximation leftOuterIndex)))
          (isWithinBoundTriangle
            (isWithinBoundTriangle firstShiftLeg secondShiftLeg)
            thirdShiftLeg)
      isWithinBoundCongrBound
        (denotesSameAsTrans
          (chainedSlackBoundReshapesDenotesSame (reciprocalOfSucc sharedIndex)
            (reciprocalOfSucc slackIndex)
            (addExact
              (addExact
                (mulExact
                  (mulExact (canonicalBound secondFactor)
                    (canonicalBound thirdFactor))
                  (ratioOfNatSucc 2 slackIndex))
                (mulExact (canonicalBound firstFactor)
                  (mulExact (canonicalBound thirdFactor)
                    (ratioOfNatSucc 2 slackIndex))))
              (mulExact (canonicalBound firstFactor)
                (mulExact (canonicalBound secondFactor)
                  (ratioOfNatSucc 2 slackIndex)))))
          (addExactRespectsDenotesSameAs
            (ratioOfNatSuccSumDenotesSame 1 1 sharedIndex)
            (denotesSameAsTrans
              (addExactRespectsDenotesSameAs
                (ratioOfNatSuccSumDenotesSame 1 1 slackIndex)
                middleBoundCollapses)
              (ratioOfNatSuccSumDenotesSame 2 middleNumerator slackIndex))))
        (isWithinBoundTriangle
          (isWithinBoundTriangle
            ((mulReal (mulReal firstFactor secondFactor) thirdFactor).isRegular
              sharedIndex slackIndex)
            compareAtSlack)
          ((mulReal firstFactor (mulReal secondFactor thirdFactor)).isRegular
            slackIndex sharedIndex)))

/-! ## Left distributivity (slack closure)

`x·(y + z)` and `x·y + x·z` sample `x` at the product index vs the two
per-summand product indices, and `y`, `z` at the ADD's doubled index vs their
product indices — distinct depths, so slack closure again.  At the slack
index the ℚ layer distributes once at the anchor (`mulExactLeftDistrib`, all
atoms at their left-hand samples); each of the two resulting products then
telescopes to its right-hand form through a mixed-middle product-difference
pair (both factors moving), the shared bound carrying the constant magnitude
and every sampling mismatch relaxed to `2/(s+1)`. -/

/-- **Left distributivity** of `·` over `+` up to the real setoid. -/
theorem mulRealLeftDistrib (factor leftSummand rightSummand : RegularReal) :
    DenotesSameReal
      (mulReal factor (addReal leftSummand rightSummand))
      (addReal (mulReal factor leftSummand) (mulReal factor rightSummand)) :=
  fun sharedIndex =>
    isWithinBoundOfForallSlack (fun slackIndex =>
      let factorSamplingIndex :=
        productSamplingIndex factor (addReal leftSummand rightSummand) slackIndex
      let doubledFactorIndex := 2 * factorSamplingIndex + 1
      let leftProductIndex :=
        productSamplingIndex factor leftSummand (2 * slackIndex + 1)
      let rightProductIndex :=
        productSamplingIndex factor rightSummand (2 * slackIndex + 1)
      let leftShiftNumerator :=
        (sharedBoundNumeratorPredecessor factor leftSummand + 1) * 2
      let rightShiftNumerator :=
        (sharedBoundNumeratorPredecessor factor rightSummand + 1) * 2
      let middleNumerator :=
        (leftShiftNumerator + leftShiftNumerator) +
          (rightShiftNumerator + rightShiftNumerator)
      have factorIsDeep : slackIndex ≤ factorSamplingIndex :=
        natSelfLeBoundScaledIndex
          (sharedBoundNumeratorPredecessor factor
            (addReal leftSummand rightSummand))
          slackIndex
      have doubledFactorIsDeep : slackIndex ≤ doubledFactorIndex :=
        natLeTrans factorIsDeep (natSelfLeDoubleSelfSucc factorSamplingIndex)
      have leftProductIsDeep : slackIndex ≤ leftProductIndex :=
        natLeTrans (natSelfLeDoubleSelfSucc slackIndex)
          (natSelfLeBoundScaledIndex
            (sharedBoundNumeratorPredecessor factor leftSummand)
            (2 * slackIndex + 1))
      have rightProductIsDeep : slackIndex ≤ rightProductIndex :=
        natLeTrans (natSelfLeDoubleSelfSucc slackIndex)
          (natSelfLeBoundScaledIndex
            (sharedBoundNumeratorPredecessor factor rightSummand)
            (2 * slackIndex + 1))
      have relaxedLeftSummandDiff :
          IsWithinBound (leftSummand.approximation doubledFactorIndex)
            (leftSummand.approximation leftProductIndex)
            (ratioOfNatSucc 2 slackIndex) :=
        isWithinBoundOfBoundLessEqual
          (sumReciprocalBelowDoubleShallow doubledFactorIsDeep leftProductIsDeep)
          (leftSummand.isRegular doubledFactorIndex leftProductIndex)
      have relaxedLeftFactorDiff :
          IsWithinBound (factor.approximation factorSamplingIndex)
            (factor.approximation leftProductIndex)
            (ratioOfNatSucc 2 slackIndex) :=
        isWithinBoundOfBoundLessEqual
          (sumReciprocalBelowDoubleShallow factorIsDeep leftProductIsDeep)
          (factor.isRegular factorSamplingIndex leftProductIndex)
      have relaxedRightSummandDiff :
          IsWithinBound (rightSummand.approximation doubledFactorIndex)
            (rightSummand.approximation rightProductIndex)
            (ratioOfNatSucc 2 slackIndex) :=
        isWithinBoundOfBoundLessEqual
          (sumReciprocalBelowDoubleShallow doubledFactorIsDeep rightProductIsDeep)
          (rightSummand.isRegular doubledFactorIndex rightProductIndex)
      have relaxedRightFactorDiff :
          IsWithinBound (factor.approximation factorSamplingIndex)
            (factor.approximation rightProductIndex)
            (ratioOfNatSucc 2 slackIndex) :=
        isWithinBoundOfBoundLessEqual
          (sumReciprocalBelowDoubleShallow factorIsDeep rightProductIsDeep)
          (factor.isRegular factorSamplingIndex rightProductIndex)
      have leftDistribLeg :
          IsWithinBound
            (mulExact (factor.approximation factorSamplingIndex)
              (leftSummand.approximation doubledFactorIndex))
            (mulExact (factor.approximation leftProductIndex)
              (leftSummand.approximation leftProductIndex))
            (addExact
              (mulExact (sharedBound factor leftSummand)
                (ratioOfNatSucc 2 slackIndex))
              (mulExact (sharedBound factor leftSummand)
                (ratioOfNatSucc 2 slackIndex))) :=
        isWithinBoundTriangle
          (mulExactRespectsIsWithinBoundLeft
            (leftApproximationIsWithinSharedBound factor leftSummand
              factorSamplingIndex)
            relaxedLeftSummandDiff
            (ratioOfNatSuccIsNonNegative 2 slackIndex))
          (mulExactRespectsIsWithinBoundRight
            (rightApproximationIsWithinSharedBound factor leftSummand
              leftProductIndex)
            relaxedLeftFactorDiff
            (ratioOfNatSuccIsNonNegative 2 slackIndex))
      have rightDistribLeg :
          IsWithinBound
            (mulExact (factor.approximation factorSamplingIndex)
              (rightSummand.approximation doubledFactorIndex))
            (mulExact (factor.approximation rightProductIndex)
              (rightSummand.approximation rightProductIndex))
            (addExact
              (mulExact (sharedBound factor rightSummand)
                (ratioOfNatSucc 2 slackIndex))
              (mulExact (sharedBound factor rightSummand)
                (ratioOfNatSucc 2 slackIndex))) :=
        isWithinBoundTriangle
          (mulExactRespectsIsWithinBoundLeft
            (leftApproximationIsWithinSharedBound factor rightSummand
              factorSamplingIndex)
            relaxedRightSummandDiff
            (ratioOfNatSuccIsNonNegative 2 slackIndex))
          (mulExactRespectsIsWithinBoundRight
            (rightApproximationIsWithinSharedBound factor rightSummand
              rightProductIndex)
            relaxedRightFactorDiff
            (ratioOfNatSuccIsNonNegative 2 slackIndex))
      have middleBoundCollapses :
          DenotesSameAs
            (addExact
              (addExact
                (mulExact (sharedBound factor leftSummand)
                  (ratioOfNatSucc 2 slackIndex))
                (mulExact (sharedBound factor leftSummand)
                  (ratioOfNatSucc 2 slackIndex)))
              (addExact
                (mulExact (sharedBound factor rightSummand)
                  (ratioOfNatSucc 2 slackIndex))
                (mulExact (sharedBound factor rightSummand)
                  (ratioOfNatSucc 2 slackIndex))))
            (ratioOfNatSucc middleNumerator slackIndex) :=
        denotesSameAsTrans
          (addExactRespectsDenotesSameAs
            (addExactRespectsDenotesSameAs
              (mulExactRatioRatioDenotesSame
                (sharedBoundNumeratorPredecessor factor leftSummand + 1) 2
                slackIndex)
              (mulExactRatioRatioDenotesSame
                (sharedBoundNumeratorPredecessor factor leftSummand + 1) 2
                slackIndex))
            (addExactRespectsDenotesSameAs
              (mulExactRatioRatioDenotesSame
                (sharedBoundNumeratorPredecessor factor rightSummand + 1) 2
                slackIndex)
              (mulExactRatioRatioDenotesSame
                (sharedBoundNumeratorPredecessor factor rightSummand + 1) 2
                slackIndex)))
          (denotesSameAsTrans
            (addExactRespectsDenotesSameAs
              (ratioOfNatSuccSumDenotesSame leftShiftNumerator leftShiftNumerator
                slackIndex)
              (ratioOfNatSuccSumDenotesSame rightShiftNumerator
                rightShiftNumerator slackIndex))
            (ratioOfNatSuccSumDenotesSame
              (leftShiftNumerator + leftShiftNumerator)
              (rightShiftNumerator + rightShiftNumerator) slackIndex))
      have compareAtSlack :
          IsWithinBound
            ((mulReal factor (addReal leftSummand rightSummand)).approximation
              slackIndex)
            ((addReal (mulReal factor leftSummand)
                (mulReal factor rightSummand)).approximation slackIndex)
            (addExact
              (addExact
                (mulExact (sharedBound factor leftSummand)
                  (ratioOfNatSucc 2 slackIndex))
                (mulExact (sharedBound factor leftSummand)
                  (ratioOfNatSucc 2 slackIndex)))
              (addExact
                (mulExact (sharedBound factor rightSummand)
                  (ratioOfNatSucc 2 slackIndex))
                (mulExact (sharedBound factor rightSummand)
                  (ratioOfNatSucc 2 slackIndex)))) :=
        isWithinBoundCongrLeft
          (denotesSameAsSymm
            (mulExactLeftDistrib (factor.approximation factorSamplingIndex)
              (leftSummand.approximation doubledFactorIndex)
              (rightSummand.approximation doubledFactorIndex)))
          (addExactRespectsIsWithinBound leftDistribLeg rightDistribLeg)
      isWithinBoundCongrBound
        (denotesSameAsTrans
          (chainedSlackBoundReshapesDenotesSame (reciprocalOfSucc sharedIndex)
            (reciprocalOfSucc slackIndex)
            (addExact
              (addExact
                (mulExact (sharedBound factor leftSummand)
                  (ratioOfNatSucc 2 slackIndex))
                (mulExact (sharedBound factor leftSummand)
                  (ratioOfNatSucc 2 slackIndex)))
              (addExact
                (mulExact (sharedBound factor rightSummand)
                  (ratioOfNatSucc 2 slackIndex))
                (mulExact (sharedBound factor rightSummand)
                  (ratioOfNatSucc 2 slackIndex)))))
          (addExactRespectsDenotesSameAs
            (ratioOfNatSuccSumDenotesSame 1 1 sharedIndex)
            (denotesSameAsTrans
              (addExactRespectsDenotesSameAs
                (ratioOfNatSuccSumDenotesSame 1 1 slackIndex)
                middleBoundCollapses)
              (ratioOfNatSuccSumDenotesSame 2 middleNumerator slackIndex))))
        (isWithinBoundTriangle
          (isWithinBoundTriangle
            ((mulReal factor (addReal leftSummand rightSummand)).isRegular
              sharedIndex slackIndex)
            compareAtSlack)
          ((addReal (mulReal factor leftSummand)
              (mulReal factor rightSummand)).isRegular slackIndex sharedIndex)))

/-- **Right distributivity** of `·` over `+` — from left distributivity and
commutativity: commute the outer product, distribute on the left, then
commute each summand product back. -/
theorem mulRealRightDistrib (leftSummand rightSummand factor : RegularReal) :
    DenotesSameReal
      (mulReal (addReal leftSummand rightSummand) factor)
      (addReal (mulReal leftSummand factor) (mulReal rightSummand factor)) :=
  denotesSameRealTrans
    (mulRealComm (addReal leftSummand rightSummand) factor)
    (denotesSameRealTrans
      (mulRealLeftDistrib factor leftSummand rightSummand)
      (addRealRespectsDenotesSame (mulRealComm factor leftSummand)
        (mulRealComm factor rightSummand)))

end FX1Poly.ComputerAlgebra
