import FX1Poly.ComputerAlgebra.Number.RegularRealArithmetic
import FX1Poly.ComputerAlgebra.Number.RegularRealCompleteness
import FX1Poly.ComputerAlgebra.Number.RegularRealOrderTightness

/-! # Real sequence limits — modulus-based convergence (ANALYSIS-LIMIT-1)

The first calculus rung.  A real sequence `sequence : Nat -> RegularReal`
CONVERGES to a limit with an EXPLICIT modulus, Bishop-style: at precision
index `k`, every member from `modulus k` onward sits within `1/(k+1)` of
the limit in the real-level distance `IsWithinRealBound`.  No unbounded
existential — the modulus IS the constructive rate, exactly as the
regularity and Cauchy certificates are baked into `RegularReal` and
`RegularRealSequence`.

The limit is UNIQUE up to `DenotesSameReal`: two limits of one sequence
are setoid-equal.  Rather than redo the diagonal-limit uniqueness bound,
the proof feeds the shipped `denotesSameRealOfSharedConvergence` a common
deep-sampled subsequence `values (firstModulus p + secondModulus p + p)`,
which the SAME sequence approaches within `1/(p+1)` toward BOTH limits.

The LIMIT LAWS: the sum of two convergent sequences converges to the sum
of the limits (combined modulus `mx (2k+1) + my (2k+1)` — a SUM, never a
`Nat.max`, so no `le_max` propext leak — with the doubled reciprocals
recombining EXACTLY by `reciprocalDoubleSumDenotesSame`), and the
negation converges to the negated limit with the SAME modulus (negation
is a pointwise isometry).  Each real-level bound-respecting lemma
generalizes the shipped `*RespectsDenotesSame` from setoid bound `0` to
an arbitrary bound `q`.  Zero axioms throughout. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## Nat monotonicity shims for SUM-form combined moduli -/

/-- A value sits below itself plus any right addend — the additive witness
is the addend. -/
theorem natSelfLeAddRight (value addend : Nat) : value ≤ value + addend :=
  Nat.le.intro rfl

/-- A value sits below any left addend plus itself — the additive witness
rides one commutation. -/
theorem natSelfLeAddLeft (value addend : Nat) : value ≤ addend + value :=
  Nat.le.intro (Nat.add_comm value addend)

/-! ## Real-level bound relaxation and congruence -/

/-- Relax a real-level bound upward — per index the setoid modulus rides
along and the pointwise bound relaxes. -/
theorem isWithinRealBoundOfBoundLessEqual
    {leftValue rightValue : RegularReal} {lowBound highBound : RationalPair}
    (isBelow : LessEqualAs lowBound highBound)
    (isWithin : IsWithinRealBound leftValue rightValue lowBound) :
    IsWithinRealBound leftValue rightValue highBound :=
  fun index =>
    isWithinBoundOfBoundLessEqual
      (addExactMonotone isBelow (lessEqualAsRefl (ratioOfNatSucc 2 index)))
      (isWithin index)

/-- The real-level bound respects the setoid — swap the bound for a
setoid-equal one, per index. -/
theorem isWithinRealBoundCongrBound {leftValue rightValue : RegularReal}
    {bound newBound : RationalPair}
    (boundsAgree : DenotesSameAs bound newBound)
    (isWithin : IsWithinRealBound leftValue rightValue bound) :
    IsWithinRealBound leftValue rightValue newBound :=
  fun index =>
    isWithinBoundCongrBound
      (addExactRespectsDenotesSameAs boundsAgree
        (denotesSameAsRefl (ratioOfNatSucc 2 index)))
      (isWithin index)

/-! ## Modulus-based convergence -/

/-- **Modulus-based convergence of a real sequence** — Bishop-style with an
EXPLICIT rate.  At precision index `k`, every member from `modulus k`
onward sits within `1/(k+1)` of the limit in the real-level distance. -/
def ConvergesTo (sequence : Nat → RegularReal) (limit : RegularReal)
    (modulus : Nat → Nat) : Prop :=
  ∀ precisionIndex position : Nat,
    modulus precisionIndex ≤ position →
      IsWithinRealBound (sequence position) limit
        (reciprocalOfSucc precisionIndex)

/-- A constant sequence converges to its value at the zero modulus — every
member is setoid-equal to the limit, so meets every reciprocal bound. -/
theorem convergesToConstant (value : RegularReal) :
    ConvergesTo (fun _ => value) value (fun _ => 0) :=
  fun precisionIndex _ _ =>
    isWithinRealBoundOfDenotesSameReal (denotesSameRealRefl value)
      (ratioOfNatSuccIsNonNegative 1 precisionIndex)

/-- **The diagonal limit converges with the identity modulus** — the shipped
tight convergence relaxed so `1/(position+1) <= 1/(k+1)` when
`position >= k`. -/
theorem convergesToLimitReal (sequence : RegularRealSequence) :
    ConvergesTo sequence.values (limitReal sequence) (fun precisionIndex => precisionIndex) :=
  fun precisionIndex position isReached =>
    isWithinRealBoundOfBoundLessEqual
      (ratioOfNatSuccAntitoneDenominator 1 isReached)
      (sequenceConvergesToLimitReal sequence position)

/-- **Modulus-form limit uniqueness** — two limits of one sequence are
setoid-equal.  The shipped `denotesSameRealOfSharedConvergence` closes it
once fed the common deep-sampled subsequence
`values (firstModulus p + secondModulus p + p)`, which the sequence
approaches within `1/(p+1)` toward BOTH limits (the deep index dominates
each modulus). -/
theorem denotesSameRealOfConvergesToBoth {values : Nat → RegularReal}
    {firstLimit secondLimit : RegularReal} {firstModulus secondModulus : Nat → Nat}
    (convergesToFirst : ConvergesTo values firstLimit firstModulus)
    (convergesToSecond : ConvergesTo values secondLimit secondModulus) :
    DenotesSameReal firstLimit secondLimit :=
  denotesSameRealOfSharedConvergence
    (fun position =>
      values (firstModulus position + secondModulus position + position))
    (fun position =>
      convergesToFirst position
        (firstModulus position + secondModulus position + position)
        (natLeTrans
          (natSelfLeAddRight (firstModulus position) (secondModulus position))
          (natSelfLeAddRight (firstModulus position + secondModulus position)
            position)))
    (fun position =>
      convergesToSecond position
        (firstModulus position + secondModulus position + position)
        (natLeTrans
          (natSelfLeAddLeft (secondModulus position) (firstModulus position))
          (natSelfLeAddRight (firstModulus position + secondModulus position)
            position)))

/-! ## Limit law: sum -/

/-- **Addition respects the real-level bound** — the abs-free parallel-add
law lifted from the setoid instance `addRealRespectsDenotesSame` (bound `0`)
to an arbitrary bound.  At each index both summands sample at `2*index+1`;
the parallel bound `(q1 + r) + (q2 + r)` regroups medially onto
`(q1 + q2) + (r + r)`, and the doubled reciprocal `r + r` recombines
EXACTLY to `2/(index+1)`. -/
theorem addRealRespectsIsWithinRealBound
    {leftA rightA leftB rightB : RegularReal}
    {firstBound secondBound : RationalPair}
    (isFirstWithin : IsWithinRealBound leftA rightA firstBound)
    (isSecondWithin : IsWithinRealBound leftB rightB secondBound) :
    IsWithinRealBound (addReal leftA leftB) (addReal rightA rightB)
      (addExact firstBound secondBound) :=
  fun index =>
    isWithinBoundCongrBound
      (denotesSameAsTrans
        (addExactMedialDenotesSame firstBound (ratioOfNatSucc 2 (2 * index + 1))
          secondBound (ratioOfNatSucc 2 (2 * index + 1)))
        (addExactRespectsDenotesSameAs
          (denotesSameAsRefl (addExact firstBound secondBound))
          (ratioTwoDoubleSumDenotesSame index)))
      (addExactRespectsIsWithinBound
        (isFirstWithin (2 * index + 1))
        (isSecondWithin (2 * index + 1)))

/-- **Limit law — sum**: the sum of two convergent sequences converges to
the sum of the limits.  Combined modulus `mx (2k+1) + my (2k+1)` (SUM-form,
propext-clean); the two `1/(2k+2)` bounds recombine EXACTLY to `1/(k+1)`. -/
theorem convergesToAddReal {sequenceLeft sequenceRight : Nat → RegularReal}
    {limitLeft limitRight : RegularReal} {modulusLeft modulusRight : Nat → Nat}
    (convergesLeft : ConvergesTo sequenceLeft limitLeft modulusLeft)
    (convergesRight : ConvergesTo sequenceRight limitRight modulusRight) :
    ConvergesTo
      (fun position => addReal (sequenceLeft position) (sequenceRight position))
      (addReal limitLeft limitRight)
      (fun precisionIndex =>
        modulusLeft (2 * precisionIndex + 1) + modulusRight (2 * precisionIndex + 1)) :=
  fun precisionIndex position isReached =>
    isWithinRealBoundCongrBound
      (reciprocalDoubleSumDenotesSame precisionIndex)
      (addRealRespectsIsWithinRealBound
        (convergesLeft (2 * precisionIndex + 1) position
          (natLeTrans
            (natSelfLeAddRight (modulusLeft (2 * precisionIndex + 1))
              (modulusRight (2 * precisionIndex + 1)))
            isReached))
        (convergesRight (2 * precisionIndex + 1) position
          (natLeTrans
            (natSelfLeAddLeft (modulusRight (2 * precisionIndex + 1))
              (modulusLeft (2 * precisionIndex + 1)))
            isReached)))

/-! ## Limit law: negation -/

/-- **Negation respects the real-level bound** — pointwise, the SAME bound;
negation is a two-sided isometry.  Generalizes the setoid instance
`negRealRespectsDenotesSame`. -/
theorem negRealRespectsIsWithinRealBound {leftValue rightValue : RegularReal}
    {bound : RationalPair}
    (isWithin : IsWithinRealBound leftValue rightValue bound) :
    IsWithinRealBound (negReal leftValue) (negReal rightValue) bound :=
  fun index => negExactRespectsIsWithinBound (isWithin index)

/-- **Limit law — negation**: the negation of a convergent sequence
converges to the negated limit with the SAME modulus. -/
theorem convergesToNegReal {sequence : Nat → RegularReal}
    {limit : RegularReal} {modulus : Nat → Nat}
    (converges : ConvergesTo sequence limit modulus) :
    ConvergesTo (fun position => negReal (sequence position)) (negReal limit)
      modulus :=
  fun precisionIndex position isReached =>
    negRealRespectsIsWithinRealBound (converges precisionIndex position isReached)

/-! ## Limit law: order preservation

The weak Bishop order `LessEqualReal` is limit-closed.  The crux is
`realNonNegativeOfConvergesTo`: nonnegativity (every difference approximant
clears the vanishing lower bound `−1/(n+1)`) transports across a modulus
limit.  Fix a comparison index `c`; slack closure at numerator `5` reduces
the goal to bounding `limit_c` below by `−1/(c+1)` up to `5/(s+1)` for every
deep sample `s`.  At `s` pick the position `modulus s`, whose member is
nonnegative at index `s`; convergence pins that member within `3/(s+1)` of
`limit_s` (`1/(s+1)` precision plus the `2/(s+1)` setoid modulus), and one
regularity step of `limit` moves `limit_s` back to `limit_c`.  The collected
tail folds to exactly `5/(s+1)` with the `1/(c+1)` regularity leftover pulled
out and cancelled — the same discipline `realNonNegativeRespectsDenotesSame`
uses, with `4 → 5` because the convergence step carries one extra reciprocal.
The order law then feeds the difference sequence
`sequenceUpper − sequenceLower` (built by `convergesToAddReal` over
`convergesToNegReal`) into this closure. -/

namespace RationalPair

/-- **The order-limit slack tail, pure**: the rational tail
`((1/(m+1) + 1/(k+1)) + 3/(m+1)) + 1/(m+1)` denotes `5/(m+1) + 1/(k+1)` —
rotate `1/(k+1)` to the far right past the three `m`-graded summands, then
fold `1/(m+1) + 3/(m+1) + 1/(m+1)` onto its shared denominator.  The
`3`-in / `5`-out sibling of `congruenceSlackTailCollapses`. -/
theorem nonNegLimitTailCollapses (outerPredecessor innerPredecessor : Nat) :
    DenotesSameAs
      (addExact
        (addExact
          (addExact (reciprocalOfSucc innerPredecessor)
            (reciprocalOfSucc outerPredecessor))
          (ratioOfNatSucc 3 innerPredecessor))
        (reciprocalOfSucc innerPredecessor))
      (addExact (ratioOfNatSucc 5 innerPredecessor)
        (reciprocalOfSucc outerPredecessor)) :=
  have innerSwap :
      DenotesSameAs
        (addExact
          (addExact (reciprocalOfSucc innerPredecessor)
            (reciprocalOfSucc outerPredecessor))
          (ratioOfNatSucc 3 innerPredecessor))
        (addExact
          (addExact (reciprocalOfSucc innerPredecessor)
            (ratioOfNatSucc 3 innerPredecessor))
          (reciprocalOfSucc outerPredecessor)) :=
    denotesSameAsTrans
      (addExactAssoc (reciprocalOfSucc innerPredecessor)
        (reciprocalOfSucc outerPredecessor)
        (ratioOfNatSucc 3 innerPredecessor))
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (denotesSameAsRefl (reciprocalOfSucc innerPredecessor))
          (addExactComm (reciprocalOfSucc outerPredecessor)
            (ratioOfNatSucc 3 innerPredecessor)))
        (denotesSameAsSymm
          (addExactAssoc (reciprocalOfSucc innerPredecessor)
            (ratioOfNatSucc 3 innerPredecessor)
            (reciprocalOfSucc outerPredecessor))))
  have rotateOuter :
      DenotesSameAs
        (addExact
          (addExact
            (addExact (reciprocalOfSucc innerPredecessor)
              (ratioOfNatSucc 3 innerPredecessor))
            (reciprocalOfSucc outerPredecessor))
          (reciprocalOfSucc innerPredecessor))
        (addExact
          (addExact
            (addExact (reciprocalOfSucc innerPredecessor)
              (ratioOfNatSucc 3 innerPredecessor))
            (reciprocalOfSucc innerPredecessor))
          (reciprocalOfSucc outerPredecessor)) :=
    denotesSameAsTrans
      (addExactAssoc
        (addExact (reciprocalOfSucc innerPredecessor)
          (ratioOfNatSucc 3 innerPredecessor))
        (reciprocalOfSucc outerPredecessor)
        (reciprocalOfSucc innerPredecessor))
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (denotesSameAsRefl
            (addExact (reciprocalOfSucc innerPredecessor)
              (ratioOfNatSucc 3 innerPredecessor)))
          (addExactComm (reciprocalOfSucc outerPredecessor)
            (reciprocalOfSucc innerPredecessor)))
        (denotesSameAsSymm
          (addExactAssoc
            (addExact (reciprocalOfSucc innerPredecessor)
              (ratioOfNatSucc 3 innerPredecessor))
            (reciprocalOfSucc innerPredecessor)
            (reciprocalOfSucc outerPredecessor))))
  have leftCollapse :
      DenotesSameAs
        (addExact
          (addExact (reciprocalOfSucc innerPredecessor)
            (ratioOfNatSucc 3 innerPredecessor))
          (reciprocalOfSucc innerPredecessor))
        (ratioOfNatSucc 5 innerPredecessor) :=
    denotesSameAsTrans
      (addExactRespectsDenotesSameAs
        (ratioOfNatSuccSumDenotesSame 1 3 innerPredecessor)
        (denotesSameAsRefl (reciprocalOfSucc innerPredecessor)))
      (ratioOfNatSuccSumDenotesSame 4 1 innerPredecessor)
  denotesSameAsTrans
    (addExactRespectsDenotesSameAs innerSwap
      (denotesSameAsRefl (reciprocalOfSucc innerPredecessor)))
    (denotesSameAsTrans rotateOuter
      (addExactRespectsDenotesSameAs leftCollapse
        (denotesSameAsRefl (reciprocalOfSucc outerPredecessor))))

/-- **The order-limit slack tail, with the carried base value**: pull the
approximant `baseValue` out front over the pure-rational tail, collapse the
tail by `nonNegLimitTailCollapses`, and re-associate onto the
`(baseValue + 5/(m+1)) + 1/(k+1)` slack shape. -/
theorem nonNegLimitTailCollapsesShaped (baseValue : RationalPair)
    (outerPredecessor innerPredecessor : Nat) :
    DenotesSameAs
      (addExact
        (addExact
          (addExact baseValue
            (addExact (reciprocalOfSucc innerPredecessor)
              (reciprocalOfSucc outerPredecessor)))
          (ratioOfNatSucc 3 innerPredecessor))
        (reciprocalOfSucc innerPredecessor))
      (addExact (addExact baseValue (ratioOfNatSucc 5 innerPredecessor))
        (reciprocalOfSucc outerPredecessor)) :=
  denotesSameAsTrans
    (addExactRespectsDenotesSameAs
      (addExactAssoc baseValue
        (addExact (reciprocalOfSucc innerPredecessor)
          (reciprocalOfSucc outerPredecessor))
        (ratioOfNatSucc 3 innerPredecessor))
      (denotesSameAsRefl (reciprocalOfSucc innerPredecessor)))
    (denotesSameAsTrans
      (addExactAssoc baseValue
        (addExact
          (addExact (reciprocalOfSucc innerPredecessor)
            (reciprocalOfSucc outerPredecessor))
          (ratioOfNatSucc 3 innerPredecessor))
        (reciprocalOfSucc innerPredecessor))
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (denotesSameAsRefl baseValue)
          (nonNegLimitTailCollapses outerPredecessor innerPredecessor))
        (denotesSameAsSymm
          (addExactAssoc baseValue (ratioOfNatSucc 5 innerPredecessor)
            (reciprocalOfSucc outerPredecessor)))))

end RationalPair

/-- **Nonnegativity is closed under modulus limits**: if every member of a
convergent sequence clears the vanishing lower bound `−1/(index+1)` at every
index, so does the limit.  Slack closure at numerator `5` reduces the bound
at comparison index `c` to, for every deep sample `s`, the chain
`−1/(s+1) ≤ member_{modulus s}(s) ≤ limit_s + 3/(s+1) ≤
(limit_c + (1/(s+1) + 1/(c+1))) + 3/(s+1)`; shifting by `1/(s+1)` and folding
the tail to `5/(s+1)` leaves exactly `−1/(c+1) ≤ limit_c + 5/(s+1)`. -/
theorem realNonNegativeOfConvergesTo {sequence : Nat → RegularReal}
    {limit : RegularReal} {modulus : Nat → Nat}
    (converges : ConvergesTo sequence limit modulus)
    (pointwiseNonNegative : ∀ position index : Nat,
      LessEqualAs (negExact (reciprocalOfSucc index))
        ((sequence position).approximation index)) :
    ∀ index : Nat,
      LessEqualAs (negExact (reciprocalOfSucc index)) (limit.approximation index) :=
  fun comparisonIndex =>
    lessEqualAsOfForallSlack (slackNumerator := 5) (fun slackIndex =>
      have convergedBound :
          IsWithinBound ((sequence (modulus slackIndex)).approximation slackIndex)
            (limit.approximation slackIndex)
            (addExact (reciprocalOfSucc slackIndex) (ratioOfNatSucc 2 slackIndex)) :=
        converges slackIndex (modulus slackIndex) (Nat.le_refl (modulus slackIndex))
          slackIndex
      have sequenceDiffBounded :
          LessEqualAs
            (subExact ((sequence (modulus slackIndex)).approximation slackIndex)
              (limit.approximation slackIndex))
            (ratioOfNatSucc 3 slackIndex) :=
        lessEqualAsCongrRight (ratioOfNatSuccSumDenotesSame 1 2 slackIndex)
          convergedBound.left
      have sequenceShunted :
          LessEqualAs ((sequence (modulus slackIndex)).approximation slackIndex)
            (addExact (limit.approximation slackIndex) (ratioOfNatSucc 3 slackIndex)) :=
        lessEqualAsAddOfSubLessEqual sequenceDiffBounded
      have regularityShunted :
          LessEqualAs (limit.approximation slackIndex)
            (addExact (limit.approximation comparisonIndex)
              (addExact (reciprocalOfSucc slackIndex)
                (reciprocalOfSucc comparisonIndex))) :=
        lessEqualAsAddOfSubLessEqual (limit.isRegular slackIndex comparisonIndex).left
      have chainThroughDeepSample :
          LessEqualAs (negExact (reciprocalOfSucc slackIndex))
            (addExact
              (addExact (limit.approximation comparisonIndex)
                (addExact (reciprocalOfSucc slackIndex)
                  (reciprocalOfSucc comparisonIndex)))
              (ratioOfNatSucc 3 slackIndex)) :=
        lessEqualAsTrans (pointwiseNonNegative (modulus slackIndex) slackIndex)
          (lessEqualAsTrans sequenceShunted
            (addExactMonotone regularityShunted
              (lessEqualAsRefl (ratioOfNatSucc 3 slackIndex))))
      have shiftedNonNegative :
          LessEqualAs zeroRational
            (addExact
              (addExact (limit.approximation comparisonIndex)
                (ratioOfNatSucc 5 slackIndex))
              (reciprocalOfSucc comparisonIndex)) :=
        lessEqualAsCongrLeft
          (addExactNegLeftDenotesSame (reciprocalOfSucc slackIndex))
          (lessEqualAsCongrRight
            (nonNegLimitTailCollapsesShaped (limit.approximation comparisonIndex)
              comparisonIndex slackIndex)
            (addExactMonotone chainThroughDeepSample
              (lessEqualAsRefl (reciprocalOfSucc slackIndex))))
      lessEqualAsAddRightCancel
        (lessEqualAsCongrLeft
          (denotesSameAsSymm
            (addExactNegLeftDenotesSame (reciprocalOfSucc comparisonIndex)))
          shiftedNonNegative))

/-- **Limit law — order preservation**: a pointwise `LessEqualReal` between two
convergent sequences lifts to their limits.  The difference sequence
`sequenceUpper − sequenceLower` converges to `limitUpper − limitLower` (via the
sum and negation limit laws), each member is nonnegative (that IS the pointwise
order hypothesis), and `realNonNegativeOfConvergesTo` carries nonnegativity to
the limit. -/
theorem lessEqualRealOfConvergesTo
    {sequenceLower sequenceUpper : Nat → RegularReal}
    {limitLower limitUpper : RegularReal} {modulusLower modulusUpper : Nat → Nat}
    (convergesLower : ConvergesTo sequenceLower limitLower modulusLower)
    (convergesUpper : ConvergesTo sequenceUpper limitUpper modulusUpper)
    (pointwiseBelow : ∀ position,
      LessEqualReal (sequenceLower position) (sequenceUpper position)) :
    LessEqualReal limitLower limitUpper :=
  realNonNegativeOfConvergesTo
    (convergesToAddReal convergesUpper (convergesToNegReal convergesLower))
    (fun position index => pointwiseBelow position index)

end FX1Poly.ComputerAlgebra
