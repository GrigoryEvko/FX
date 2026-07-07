import FX1Poly.ComputerAlgebra.Analysis.RealLimit
import FX1Poly.ComputerAlgebra.Number.RegularRealMultiplication

/-! # Real multiplicative limit laws — the product and scalar rungs
    (ANALYSIS-MULLIMIT-1)

The multiplicative core of the calculus foundation, and the genuine analytic
content the `RealContinuity` honest-scope note deferred: reworking the shipped
`mulRealRespectsDenotesSame` from a SHRINKING setoid bound (bound `0`) to a
FIXED continuity bound `q`.  Once that real-level product-difference law is in
hand, the product limit law, the scalar limit law, and (in the sibling
continuity module) bounded-domain multiplication continuity all fall out.

The telescope is `x_n y_n - a b = x_n (y_n - b) + (x_n - a) b`, so

    |x_n y_n - a b| <= |x_n| |y_n - b| + |b| |x_n - a|.

`mulRealRespectsIsWithinRealBound` proves exactly this at the real level: with
a UNIFORM magnitude bound `M` on the left sequence (nat ratio) and `L` on the
right limit (nat ratio), the product of two reals within `leftEps` / `rightEps`
of their limits lands within `M * rightEps + L * leftEps`.  Its proof is a
faithful generalisation of `mulRealRespectsDenotesSame`: the slack-closure
skeleton is identical, but the two mismatched-sampling factor differences relax
to `eps + 4/(slack+1)` (fixed eps plus vanishing slack) instead of the pure
`4/(slack+1)`, and the middle bound carries `bound + (4M + 4L)/(slack+1)` so the
non-vanishing `bound` survives while the nat-numerator slack closes.

The UNIFORM bound comes from `convergentSequenceIsBounded`: a convergent real
sequence is uniformly magnitude-bounded, its tail dominated by the limit's
canonical bound plus `3` (the worst `1 + 2/(index+1)` drift at precision `0`)
and its finite prefix dominated by a structural SUM of the per-member canonical
bounds — never a `Nat.max`, so no `le_max` propext leak.

The product law `convergesToMulReal` samples the two convergence hypotheses at
bound-scaled precision indices so that `M * rightEps` and `L * leftEps` each
collapse EXACTLY to `1/(2k+2)` and recombine to `1/(k+1)`.  The scalar law
`convergesToScalarMulReal` is the product law fed a constant left sequence.

Zero axioms throughout. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## Additive-monoid reshaping shims -/

namespace RationalPair

/-- Rotate an outer summand past a leading eps: `outer + (eps + inner)` denotes
`eps + (outer + inner)` — associate down, commute the leading pair, associate
back. -/
theorem addExactSwapOuterIntoInner (outerPiece epsPiece innerPiece : RationalPair) :
    DenotesSameAs (addExact outerPiece (addExact epsPiece innerPiece))
      (addExact epsPiece (addExact outerPiece innerPiece)) :=
  denotesSameAsTrans
    (denotesSameAsSymm (addExactAssoc outerPiece epsPiece innerPiece))
    (denotesSameAsTrans
      (addExactRespectsDenotesSameAs (addExactComm outerPiece epsPiece)
        (denotesSameAsRefl innerPiece))
      (addExactAssoc epsPiece outerPiece innerPiece))

/-- **The four-atom gather**: `a + (b + (c + d))` denotes `(c + a) + (b + d)` —
pull `c` to the front and pair the remaining slack pieces.  Threads the
non-vanishing bound `c` out of the middle so the vanishing pieces `b`, `d`
collect for slack closure. -/
theorem addExactGatherDenotesSame (firstPiece secondPiece thirdPiece fourthPiece :
    RationalPair) :
    DenotesSameAs
      (addExact firstPiece
        (addExact secondPiece (addExact thirdPiece fourthPiece)))
      (addExact (addExact thirdPiece firstPiece)
        (addExact secondPiece fourthPiece)) :=
  denotesSameAsTrans
    (addExactRespectsDenotesSameAs (denotesSameAsRefl firstPiece)
      (denotesSameAsTrans
        (denotesSameAsSymm (addExactAssoc secondPiece thirdPiece fourthPiece))
        (denotesSameAsTrans
          (addExactRespectsDenotesSameAs (addExactComm secondPiece thirdPiece)
            (denotesSameAsRefl fourthPiece))
          (addExactAssoc thirdPiece secondPiece fourthPiece))))
    (denotesSameAsTrans
      (denotesSameAsSymm
        (addExactAssoc firstPiece thirdPiece (addExact secondPiece fourthPiece)))
      (addExactRespectsDenotesSameAs (addExactComm firstPiece thirdPiece)
        (denotesSameAsRefl (addExact secondPiece fourthPiece))))

end RationalPair

/-! ## Uniform magnitude bound of a convergent sequence -/

/-- **The convergent tail is uniformly bounded**: for every member from
`modulus 0` onward, and at every approximation index, the magnitude sits within
`(canonicalBoundNumerator limit + 3)/1`.  At precision `0` the member sits
within `1 + 2/(index+1) <= 3` of the limit, whose approximant sits within its
canonical bound; the magnitude triangle adds the two.  This is the only piece on
the product-law critical path. -/
theorem convergentTailIsBounded {sequence : Nat → RegularReal} {limit : RegularReal}
    {modulus : Nat → Nat} (converges : ConvergesTo sequence limit modulus)
    (position : Nat) (isTail : modulus 0 ≤ position) (index : Nat) :
    IsMagnitudeWithin ((sequence position).approximation index)
      (ratioOfNatSucc (canonicalBoundNumerator limit + 3) 0) :=
  have distanceWithin :
      IsWithinBound ((sequence position).approximation index)
        (limit.approximation index)
        (addExact (reciprocalOfSucc 0) (ratioOfNatSucc 2 index)) :=
    converges 0 position isTail index
  have relaxDistanceBound :
      LessEqualAs (addExact (reciprocalOfSucc 0) (ratioOfNatSucc 2 index))
        (ratioOfNatSucc 3 0) :=
    lessEqualAsCongrRight (ratioOfNatSuccSumDenotesSame 1 2 0)
      (addExactMonotone (lessEqualAsRefl (reciprocalOfSucc 0))
        (ratioOfNatSuccAntitoneDenominator 2 (Nat.zero_le index)))
  have relaxedDistance :
      IsWithinBound ((sequence position).approximation index)
        (limit.approximation index) (ratioOfNatSucc 3 0) :=
    isWithinBoundOfBoundLessEqual relaxDistanceBound distanceWithin
  have triangle :
      IsMagnitudeWithin ((sequence position).approximation index)
        (addExact (canonicalBound limit) (ratioOfNatSucc 3 0)) :=
    isMagnitudeWithinTriangle relaxedDistance
      (approximationIsWithinCanonicalBound limit index)
  isMagnitudeWithinCongrBound
    (ratioOfNatSuccSumDenotesSame (canonicalBoundNumerator limit) 3 0) triangle

/-- A structural prefix sum: `sum_{i < count} valueOf i` — the finite-prefix
dominator, a SUM (never a `Nat.max`). -/
def sumOverPrefix : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | count + 1, valueOf => sumOverPrefix count valueOf + valueOf count

/-- **Every prefix member sits below the prefix sum** — structural induction on
`count`, the successor step landing the last member on the tail addend and every
earlier member on the accumulated head. -/
theorem natMemberLeSumOverPrefix (valueOf : Nat → Nat) :
    ∀ count position : Nat, position < count →
      valueOf position ≤ sumOverPrefix count valueOf
  | 0, position, isBelow => absurd isBelow (Nat.not_lt_zero position)
  | count + 1, position, isBelow =>
      match Nat.lt_or_ge position count with
      | Or.inl isBelowCount =>
          natLeTrans (natMemberLeSumOverPrefix valueOf count position isBelowCount)
            (natSelfLeAddRight (sumOverPrefix count valueOf) (valueOf count))
      | Or.inr isAtLeastCount =>
          natLeOfEqLeft
            (congrArg valueOf (Nat.le_antisymm (Nat.le_of_lt_succ isBelow) isAtLeastCount))
            (natSelfLeAddLeft (valueOf count) (sumOverPrefix count valueOf))

/-- **A convergent real sequence is uniformly magnitude-bounded** across ALL
positions and approximation indices.  The bound numerator is the tail dominator
`(canonicalBoundNumerator limit + 3)` plus the structural prefix sum of the
finitely-many pre-tail members' canonical bounds — the tail branch dominated by
the first summand, the prefix branch by the second (via `natMemberLeSumOverPrefix`).
Never a `Nat.max`. -/
theorem convergentSequenceIsBounded {sequence : Nat → RegularReal}
    {limit : RegularReal} {modulus : Nat → Nat}
    (converges : ConvergesTo sequence limit modulus) :
    ∀ position index : Nat,
      IsMagnitudeWithin ((sequence position).approximation index)
        (ratioOfNatSucc
          ((canonicalBoundNumerator limit + 3) +
            sumOverPrefix (modulus 0)
              (fun prefixPosition => canonicalBoundNumerator (sequence prefixPosition)))
          0) :=
  fun position index =>
    match Nat.lt_or_ge position (modulus 0) with
    | Or.inl isPrefix =>
        isMagnitudeWithinOfBoundLessEqual
          (ratioOfNatSuccMonotoneNumerator
            (natLeTrans
              (natMemberLeSumOverPrefix
                (fun prefixPosition => canonicalBoundNumerator (sequence prefixPosition))
                (modulus 0) position isPrefix)
              (natSelfLeAddLeft
                (sumOverPrefix (modulus 0)
                  (fun prefixPosition =>
                    canonicalBoundNumerator (sequence prefixPosition)))
                (canonicalBoundNumerator limit + 3)))
            0)
          (approximationIsWithinCanonicalBound (sequence position) index)
    | Or.inr isTail =>
        isMagnitudeWithinOfBoundLessEqual
          (ratioOfNatSuccMonotoneNumerator
            (natSelfLeAddRight (canonicalBoundNumerator limit + 3)
              (sumOverPrefix (modulus 0)
                (fun prefixPosition => canonicalBoundNumerator (sequence prefixPosition))))
            0)
          (convergentTailIsBounded converges position isTail index)

/-! ## The real-level product-difference law (the deferred analytic core) -/

/-- **Multiplication respects the real-level bound** — the FIXED-bound
generalisation of `mulRealRespectsDenotesSame`.  With `M = multiplierBoundNumerator/1`
a uniform magnitude bound on the left sequence and `L = limitBoundNumerator/1` a
uniform magnitude bound on the right limit, two products of `leftEps` / `rightEps`
-close factors land within `M * rightEps + L * leftEps`.

The slack-closure skeleton mirrors `mulRealRespectsDenotesSame` exactly: per
shared index, both products chain to the slack index by their own regularity;
there the mixed middle `leftSeq(old) * rightLim(new)` splits the difference into
two product-difference legs at the uniform bounds; each factor difference bridges
its sampling mismatch by regularity and lands on the fixed `eps` plus a vanishing
`4/(slack+1)`; the middle bound carries `(M rightEps + L leftEps) +
(4M + 4L)/(slack+1)`, and the accumulated chain reshapes onto
`(M rightEps + L leftEps) + 2/(shared+1)` plus a nat-numerator vanishing slack
that closes. -/
theorem mulRealRespectsIsWithinRealBound
    {leftSeq leftLim rightSeq rightLim : RegularReal}
    {leftEps rightEps : RationalPair}
    (multiplierBoundNumerator limitBoundNumerator : Nat)
    (leftMagnitude : ∀ index,
      IsMagnitudeWithin (leftSeq.approximation index)
        (ratioOfNatSucc multiplierBoundNumerator 0))
    (limitMagnitude : ∀ index,
      IsMagnitudeWithin (rightLim.approximation index)
        (ratioOfNatSucc limitBoundNumerator 0))
    (leftClose : IsWithinRealBound leftSeq leftLim leftEps)
    (rightClose : IsWithinRealBound rightSeq rightLim rightEps)
    (isLeftEpsNonNegative : IsNonNegative leftEps)
    (isRightEpsNonNegative : IsNonNegative rightEps) :
    IsWithinRealBound (mulReal leftSeq rightSeq) (mulReal leftLim rightLim)
      (addExact (mulExact (ratioOfNatSucc multiplierBoundNumerator 0) rightEps)
        (mulExact (ratioOfNatSucc limitBoundNumerator 0) leftEps)) :=
  let multiplierBound := ratioOfNatSucc multiplierBoundNumerator 0
  let limitBound := ratioOfNatSucc limitBoundNumerator 0
  let realBound := addExact (mulExact multiplierBound rightEps)
    (mulExact limitBound leftEps)
  fun sharedIndex =>
    isWithinBoundOfForallSlack
      (slackNumerator := 2 + (multiplierBoundNumerator * 4 + limitBoundNumerator * 4))
      (fun slackIndex =>
        let oldSampling := productSamplingIndex leftSeq rightSeq slackIndex
        let newSampling := productSamplingIndex leftLim rightLim slackIndex
        let slackTerm :=
          ratioOfNatSucc (multiplierBoundNumerator * 4 + limitBoundNumerator * 4)
            slackIndex
        have tailBoundToFourSlack :
            LessEqualAs
              (addExact
                (addExact (reciprocalOfSucc oldSampling)
                  (reciprocalOfSucc newSampling))
                (ratioOfNatSucc 2 newSampling))
              (ratioOfNatSucc 4 slackIndex) :=
          lessEqualAsCongrRight
            (denotesSameAsTrans
              (addExactRespectsDenotesSameAs
                (ratioOfNatSuccSumDenotesSame 1 1 slackIndex)
                (denotesSameAsRefl (ratioOfNatSucc 2 slackIndex)))
              (ratioOfNatSuccSumDenotesSame 2 2 slackIndex))
            (addExactMonotone
              (addExactMonotone
                (ratioOfNatSuccAntitoneDenominator 1
                  (natSelfLeBoundScaledIndex
                    (sharedBoundNumeratorPredecessor leftSeq rightSeq) slackIndex))
                (ratioOfNatSuccAntitoneDenominator 1
                  (natSelfLeBoundScaledIndex
                    (sharedBoundNumeratorPredecessor leftLim rightLim) slackIndex)))
              (ratioOfNatSuccAntitoneDenominator 2
                (natSelfLeBoundScaledIndex
                  (sharedBoundNumeratorPredecessor leftLim rightLim) slackIndex)))
        have rightFactorsDiffer :
            IsWithinBound (rightSeq.approximation oldSampling)
              (rightLim.approximation newSampling)
              (addExact rightEps (ratioOfNatSucc 4 slackIndex)) :=
          isWithinBoundOfBoundLessEqual
            (lessEqualAsCongrLeft
              (denotesSameAsSymm
                (addExactSwapOuterIntoInner
                  (addExact (reciprocalOfSucc oldSampling)
                    (reciprocalOfSucc newSampling))
                  rightEps (ratioOfNatSucc 2 newSampling)))
              (addExactMonotone (lessEqualAsRefl rightEps) tailBoundToFourSlack))
            (isWithinBoundTriangle
              (rightSeq.isRegular oldSampling newSampling)
              (rightClose newSampling))
        have leftFactorsDiffer :
            IsWithinBound (leftSeq.approximation oldSampling)
              (leftLim.approximation newSampling)
              (addExact leftEps (ratioOfNatSucc 4 slackIndex)) :=
          isWithinBoundOfBoundLessEqual
            (lessEqualAsCongrLeft
              (denotesSameAsSymm
                (addExactSwapOuterIntoInner
                  (addExact (reciprocalOfSucc oldSampling)
                    (reciprocalOfSucc newSampling))
                  leftEps (ratioOfNatSucc 2 newSampling)))
              (addExactMonotone (lessEqualAsRefl leftEps) tailBoundToFourSlack))
            (isWithinBoundTriangle
              (leftSeq.isRegular oldSampling newSampling)
              (leftClose newSampling))
        have productsRaw :
            IsWithinBound
              ((mulReal leftSeq rightSeq).approximation slackIndex)
              ((mulReal leftLim rightLim).approximation slackIndex)
              (addExact
                (mulExact multiplierBound
                  (addExact rightEps (ratioOfNatSucc 4 slackIndex)))
                (mulExact limitBound
                  (addExact leftEps (ratioOfNatSucc 4 slackIndex)))) :=
          isWithinBoundTriangle
            (mulExactRespectsIsWithinBoundLeft (leftMagnitude oldSampling)
              rightFactorsDiffer
              (addExactIsNonNegative isRightEpsNonNegative
                (ratioOfNatSuccIsNonNegative 4 slackIndex)))
            (mulExactRespectsIsWithinBoundRight (limitMagnitude newSampling)
              leftFactorsDiffer
              (addExactIsNonNegative isLeftEpsNonNegative
                (ratioOfNatSuccIsNonNegative 4 slackIndex)))
        have middleReshapes :
            DenotesSameAs
              (addExact
                (mulExact multiplierBound
                  (addExact rightEps (ratioOfNatSucc 4 slackIndex)))
                (mulExact limitBound
                  (addExact leftEps (ratioOfNatSucc 4 slackIndex))))
              (addExact realBound slackTerm) :=
          denotesSameAsTrans
            (addExactRespectsDenotesSameAs
              (denotesSameAsTrans
                (mulExactLeftDistrib multiplierBound rightEps
                  (ratioOfNatSucc 4 slackIndex))
                (addExactRespectsDenotesSameAs
                  (denotesSameAsRefl (mulExact multiplierBound rightEps))
                  (mulExactRatioRatioDenotesSame multiplierBoundNumerator 4
                    slackIndex)))
              (denotesSameAsTrans
                (mulExactLeftDistrib limitBound leftEps
                  (ratioOfNatSucc 4 slackIndex))
                (addExactRespectsDenotesSameAs
                  (denotesSameAsRefl (mulExact limitBound leftEps))
                  (mulExactRatioRatioDenotesSame limitBoundNumerator 4 slackIndex))))
            (denotesSameAsTrans
              (addExactMedialDenotesSame (mulExact multiplierBound rightEps)
                (ratioOfNatSucc (multiplierBoundNumerator * 4) slackIndex)
                (mulExact limitBound leftEps)
                (ratioOfNatSucc (limitBoundNumerator * 4) slackIndex))
              (addExactRespectsDenotesSameAs (denotesSameAsRefl realBound)
                (ratioOfNatSuccSumDenotesSame (multiplierBoundNumerator * 4)
                  (limitBoundNumerator * 4) slackIndex)))
        have productsDifferAtSlack :
            IsWithinBound
              ((mulReal leftSeq rightSeq).approximation slackIndex)
              ((mulReal leftLim rightLim).approximation slackIndex)
              (addExact realBound slackTerm) :=
          isWithinBoundCongrBound middleReshapes productsRaw
        isWithinBoundCongrBound
          (denotesSameAsTrans
            (chainedSlackBoundReshapesDenotesSame
              (reciprocalOfSucc sharedIndex) (reciprocalOfSucc slackIndex)
              (addExact realBound slackTerm))
            (denotesSameAsTrans
              (addExactGatherDenotesSame
                (addExact (reciprocalOfSucc sharedIndex)
                  (reciprocalOfSucc sharedIndex))
                (addExact (reciprocalOfSucc slackIndex)
                  (reciprocalOfSucc slackIndex))
                realBound slackTerm)
              (addExactRespectsDenotesSameAs
                (addExactRespectsDenotesSameAs (denotesSameAsRefl realBound)
                  (ratioOfNatSuccSumDenotesSame 1 1 sharedIndex))
                (denotesSameAsTrans
                  (addExactRespectsDenotesSameAs
                    (ratioOfNatSuccSumDenotesSame 1 1 slackIndex)
                    (denotesSameAsRefl slackTerm))
                  (ratioOfNatSuccSumDenotesSame 2
                    (multiplierBoundNumerator * 4 + limitBoundNumerator * 4)
                    slackIndex)))))
          (isWithinBoundTriangle
            (isWithinBoundTriangle
              ((mulReal leftSeq rightSeq).isRegular sharedIndex slackIndex)
              productsDifferAtSlack)
            ((mulReal leftLim rightLim).isRegular slackIndex sharedIndex)))

/-! ## The product limit law -/

/-- The canonical bound numerator's predecessor — `natAbs (numerator x_0) + 1`,
so `canonicalBoundNumeratorPredecessor value + 1` is DEFINITIONALLY
`canonicalBoundNumerator value` and the scale collapse matches. -/
def canonicalBoundNumeratorPredecessor (value : RegularReal) : Nat :=
  (value.approximation 0).numerator.natAbs + 1

/-- **Limit law — product**: the product of two convergent sequences converges
to the product of the limits.  The left sequence is uniformly bounded by
`(canonicalBoundNumerator limitLeft + 3)/1` on its tail; the right limit by its
canonical bound.  The combined modulus (SUM-form, propext-clean) samples each
convergence at a bound-scaled precision so that `M * rightEps` and `L * leftEps`
collapse to `1/(2k+2)` and recombine EXACTLY to `1/(k+1)`, plus a third summand
`modulusLeft 0` forcing the tail bound valid. -/
theorem convergesToMulReal {sequenceLeft sequenceRight : Nat → RegularReal}
    {limitLeft limitRight : RegularReal} {modulusLeft modulusRight : Nat → Nat}
    (convergesLeft : ConvergesTo sequenceLeft limitLeft modulusLeft)
    (convergesRight : ConvergesTo sequenceRight limitRight modulusRight) :
    ConvergesTo
      (fun position => mulReal (sequenceLeft position) (sequenceRight position))
      (mulReal limitLeft limitRight)
      (fun precisionIndex =>
        modulusRight
            (boundScaledIndex (canonicalBoundNumerator limitLeft + 2) precisionIndex)
          + modulusLeft
              (boundScaledIndex (canonicalBoundNumeratorPredecessor limitRight)
                precisionIndex)
          + modulusLeft 0) :=
  fun precisionIndex position isReached =>
    let rightScaledIndex :=
      boundScaledIndex (canonicalBoundNumerator limitLeft + 2) precisionIndex
    let leftScaledIndex :=
      boundScaledIndex (canonicalBoundNumeratorPredecessor limitRight) precisionIndex
    have reachRight : modulusRight rightScaledIndex ≤ position :=
      natLeTrans
        (natLeTrans
          (natSelfLeAddRight (modulusRight rightScaledIndex)
            (modulusLeft leftScaledIndex))
          (natSelfLeAddRight
            (modulusRight rightScaledIndex + modulusLeft leftScaledIndex)
            (modulusLeft 0)))
        isReached
    have reachLeft : modulusLeft leftScaledIndex ≤ position :=
      natLeTrans
        (natLeTrans
          (natSelfLeAddLeft (modulusLeft leftScaledIndex)
            (modulusRight rightScaledIndex))
          (natSelfLeAddRight
            (modulusRight rightScaledIndex + modulusLeft leftScaledIndex)
            (modulusLeft 0)))
        isReached
    have reachTail : modulusLeft 0 ≤ position :=
      natLeTrans
        (natSelfLeAddLeft (modulusLeft 0)
          (modulusRight rightScaledIndex + modulusLeft leftScaledIndex))
        isReached
    isWithinRealBoundCongrBound
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (mulRatioReciprocalScaledCollapses (canonicalBoundNumerator limitLeft + 2)
            precisionIndex)
          (mulRatioReciprocalScaledCollapses
            (canonicalBoundNumeratorPredecessor limitRight) precisionIndex))
        (reciprocalDoubleSumDenotesSame precisionIndex))
      (mulRealRespectsIsWithinRealBound
        (canonicalBoundNumerator limitLeft + 3) (canonicalBoundNumerator limitRight)
        (fun index => convergentTailIsBounded convergesLeft position reachTail index)
        (fun index => approximationIsWithinCanonicalBound limitRight index)
        (convergesLeft leftScaledIndex position reachLeft)
        (convergesRight rightScaledIndex position reachRight)
        (ratioOfNatSuccIsNonNegative 1 leftScaledIndex)
        (ratioOfNatSuccIsNonNegative 1 rightScaledIndex))

/-! ## The scalar limit law -/

/-- **Limit law — scalar (left factor)**: multiplying a convergent sequence by a
fixed real converges to the fixed real times the limit.  The product law fed a
constant left sequence — the constant converges at the zero modulus, so the
combined modulus collapses to the right sequence's, pre-composed with the
factor's bound scale. -/
theorem convergesToScalarMulReal {factor : RegularReal}
    {sequence : Nat → RegularReal} {limit : RegularReal} {modulus : Nat → Nat}
    (converges : ConvergesTo sequence limit modulus) :
    ConvergesTo (fun position => mulReal factor (sequence position))
      (mulReal factor limit)
      (fun precisionIndex =>
        modulus
            (boundScaledIndex (canonicalBoundNumerator factor + 2) precisionIndex)
          + 0 + 0) :=
  convergesToMulReal (convergesToConstant factor) converges

end FX1Poly.ComputerAlgebra
