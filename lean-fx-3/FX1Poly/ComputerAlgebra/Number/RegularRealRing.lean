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

end FX1Poly.ComputerAlgebra
