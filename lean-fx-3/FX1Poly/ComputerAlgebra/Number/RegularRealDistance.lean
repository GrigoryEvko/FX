import FX1Poly.ComputerAlgebra.Number.RegularReal

/-! # RegularReal distance — the real-level within-bound predicate

The real-level distance predicate underlying completeness.  `IsWithinRealBound l r q`
says every pair of approximants at a shared index sits within
`q + 2/(n+1)` — Bishop's pointwise distance bound, abs-free, with the
setoid modulus as the per-index tolerance.  `DenotesSameReal` is
exactly the zero-bound instance (the zero addend collapses), and a
setoid-equal pair meets every nonnegative real-level bound.

The workhorse is the REAL-level slack closure: a bound that holds with
every rational slack holds outright.  Per index, the slack term is
reassociated past the setoid modulus and the ℚ-level Archimedean
closure fires — a decision plus saturation, no limit, no choice.  The
diagonal-limit regularity and the convergence theorem both close
through this principle. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-- **The real-level distance bound** — at every shared index the
approximants sit within the bound plus the setoid modulus. -/
def IsWithinRealBound (leftValue rightValue : RegularReal)
    (bound : RationalPair) : Prop :=
  ∀ index : Nat,
    IsWithinBound (leftValue.approximation index)
      (rightValue.approximation index)
      (addExact bound (ratioOfNatSucc 2 index))

/-- Symmetry — the pointwise bound swaps. -/
theorem isWithinRealBoundSymm {leftValue rightValue : RegularReal}
    {bound : RationalPair}
    (isWithin : IsWithinRealBound leftValue rightValue bound) :
    IsWithinRealBound rightValue leftValue bound :=
  fun index => isWithinBoundSymm (isWithin index)

/-- Setoid-equal reals meet every nonnegative real-level bound — the
setoid modulus widens to the bound plus itself. -/
theorem isWithinRealBoundOfDenotesSameReal
    {leftValue rightValue : RegularReal} {bound : RationalPair}
    (areSame : DenotesSameReal leftValue rightValue)
    (isBoundNonNegative : IsNonNegative bound) :
    IsWithinRealBound leftValue rightValue bound :=
  fun index =>
    isWithinBoundOfBoundLessEqual
      (lessEqualAsCongrLeft (addExactZeroLeft (ratioOfNatSucc 2 index))
        (addExactMonotone isBoundNonNegative
          (lessEqualAsRefl (ratioOfNatSucc 2 index))))
      (areSame index)

/-- The zero-bound instance IS the setoid — the zero addend collapses
onto the setoid modulus. -/
theorem denotesSameRealOfIsWithinRealBoundZero
    {leftValue rightValue : RegularReal}
    (isWithin : IsWithinRealBound leftValue rightValue zeroRational) :
    DenotesSameReal leftValue rightValue :=
  fun sharedIndex =>
    isWithinBoundCongrBound
      (addExactZeroLeft (ratioOfNatSucc 2 sharedIndex))
      (isWithin sharedIndex)

/-- **Real-level slack closure**: a real-level bound that holds with
every rational slack holds outright.  Per index, the slack addend is
reassociated past the setoid modulus — `(q + σ) + τ ~ (q + τ) + σ` —
and the ℚ-level Archimedean closure erases it. -/
theorem isWithinRealBoundOfForallSlack
    {leftValue rightValue : RegularReal} {bound : RationalPair}
    {slackNumerator : Nat}
    (isWithinWithSlack : ∀ slackIndex : Nat,
      IsWithinRealBound leftValue rightValue
        (addExact bound (ratioOfNatSucc slackNumerator slackIndex))) :
    IsWithinRealBound leftValue rightValue bound :=
  fun index =>
    isWithinBoundOfForallSlack (fun slackIndex =>
      isWithinBoundCongrBound
        (denotesSameAsTrans
          (addExactAssoc bound (ratioOfNatSucc slackNumerator slackIndex)
            (ratioOfNatSucc 2 index))
          (denotesSameAsTrans
            (addExactRespectsDenotesSameAs (denotesSameAsRefl bound)
              (addExactComm (ratioOfNatSucc slackNumerator slackIndex)
                (ratioOfNatSucc 2 index)))
            (denotesSameAsSymm
              (addExactAssoc bound (ratioOfNatSucc 2 index)
                (ratioOfNatSucc slackNumerator slackIndex)))))
        (isWithinWithSlack slackIndex index))

end FX1Poly.ComputerAlgebra
