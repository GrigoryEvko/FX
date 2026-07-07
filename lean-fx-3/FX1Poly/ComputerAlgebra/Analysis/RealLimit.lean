import FX1Poly.ComputerAlgebra.Number.RegularRealArithmetic
import FX1Poly.ComputerAlgebra.Number.RegularRealCompleteness

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

end FX1Poly.ComputerAlgebra
