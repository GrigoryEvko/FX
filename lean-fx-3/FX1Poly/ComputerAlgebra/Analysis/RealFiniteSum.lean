import FX1Poly.ComputerAlgebra.Analysis.RealLimit
import FX1Poly.ComputerAlgebra.Number.RegularRealRing
import FX1Poly.ComputerAlgebra.Number.ComplexRealTriangleInequality
import FX1Poly.ComputerAlgebra.Number.RegularRealAbsoluteValue

/-! # Real finite sums — the prefix fold over ℝ (ANALYSIS-FINSUM-1)

The finite-summation substrate the integral rung rests on.  `sumReal count term`
folds the first `count` reals of a sequence with `addReal`, base
`constantReal zeroRational`.  Every law is a structural `Nat` induction over the
count, dispatched to the shipped ring / bound corpus:

  * **respects the setoid** — pointwise `DenotesSameReal` lifts to the sum;
  * **additivity** `Sigma (f + g) ~ Sigma f + Sigma g` — the medial regroup;
  * **scalar pull** `Sigma (c * f) ~ c * Sigma f` — left-distribution;
  * **respects the real-level bound** — a uniform per-term bound `q` lifts to
    the `count`-scaled bound `natScaleRational count q`, built predecessor-shaped
    so the inductive step is a single `addRealRespectsIsWithinRealBound`;
  * **the cut split** `Sigma_{m+n} f ~ Sigma_m f + Sigma_n (f shifted by m)` —
    associativity over the appended tail;
  * **the block regroup** `Sigma_{k*c} f ~ Sigma_c (Sigma_k (f at k*i+j))` — the
    product reindex, with the count written `k * c` so `k*(c+1)` reduces
    DEFINITIONALLY to `k*c + k` and the step is one cut split.

The block regroup is the genuine combinatorial content the Riemann refinement
estimate consumes; keeping the outer factor on the LEFT (`k * c`) makes the
`Nat.mul` recursion land on the count, so no `Nat.succ_mul` rewrite (and its
propext risk) is ever needed.  Zero axioms throughout. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## The prefix fold -/

/-- **The finite prefix sum** — fold the first `count` reals with `addReal`,
starting from the real zero. -/
def sumReal (count : Nat) (term : Nat → RegularReal) : RegularReal :=
  match count with
  | 0 => constantReal zeroRational
  | count + 1 => addReal (sumReal count term) (term count)

/-- The empty sum is the real zero — definitional. -/
theorem sumRealZero (term : Nat → RegularReal) :
    sumReal 0 term = constantReal zeroRational := rfl

/-- The successor sum appends the next term — definitional. -/
theorem sumRealSucc (count : Nat) (term : Nat → RegularReal) :
    sumReal (count + 1) term = addReal (sumReal count term) (term count) := rfl

/-! ## Setoid congruence -/

/-- **The sum respects the real setoid** — a pointwise `DenotesSameReal` between
the two term sequences lifts to the sums. -/
theorem sumRealRespectsDenotesSame {leftTerm rightTerm : Nat → RegularReal}
    (termsAgree : ∀ position, DenotesSameReal (leftTerm position) (rightTerm position))
    (count : Nat) :
    DenotesSameReal (sumReal count leftTerm) (sumReal count rightTerm) :=
  match count with
  | 0 => denotesSameRealRefl (constantReal zeroRational)
  | count + 1 =>
      addRealRespectsDenotesSame
        (sumRealRespectsDenotesSame termsAgree count)
        (termsAgree count)

/-! ## Additivity -/

/-- **The sum is additive** — the sum of a pointwise-added sequence denotes the
sum of the two sums, by the medial regroup of the appended pairs. -/
theorem sumRealAddReal (leftTerm rightTerm : Nat → RegularReal) (count : Nat) :
    DenotesSameReal
      (sumReal count (fun position => addReal (leftTerm position) (rightTerm position)))
      (addReal (sumReal count leftTerm) (sumReal count rightTerm)) :=
  match count with
  | 0 =>
      denotesSameRealSymm (addRealZeroLeft (constantReal zeroRational))
  | count + 1 =>
      denotesSameRealTrans
        (addRealRespectsDenotesSame
          (sumRealAddReal leftTerm rightTerm count)
          (denotesSameRealRefl (addReal (leftTerm count) (rightTerm count))))
        (addRealMedial (sumReal count leftTerm) (sumReal count rightTerm)
          (leftTerm count) (rightTerm count))

/-! ## Scalar pull -/

/-- **The scalar factor pulls out of the sum** — left-distribution of a fixed
real factor over the appended tail. -/
theorem sumRealScalarMulReal (factor : RegularReal) (term : Nat → RegularReal)
    (count : Nat) :
    DenotesSameReal
      (sumReal count (fun position => mulReal factor (term position)))
      (mulReal factor (sumReal count term)) :=
  match count with
  | 0 =>
      denotesSameRealSymm (mulRealZeroRight factor)
  | count + 1 =>
      denotesSameRealTrans
        (addRealRespectsDenotesSame
          (sumRealScalarMulReal factor term count)
          (denotesSameRealRefl (mulReal factor (term count))))
        (denotesSameRealSymm
          (mulRealLeftDistrib factor (sumReal count term) (term count)))

/-- **Negation pulls out of the sum** — the finite sum of negated terms is the
negation of the sum.  Structural induction: the empty sum is `-0 ~ 0`; the
successor step distributes `negReal` over the appended `addReal`. -/
theorem sumRealNegReal (term : Nat → RegularReal) (count : Nat) :
    DenotesSameReal
      (sumReal count (fun position => negReal (term position)))
      (negReal (sumReal count term)) :=
  match count with
  | 0 =>
      denotesSameRealTrans
        (denotesSameRealSymm (addRealNegRight (constantReal zeroRational)))
        (addRealZeroLeft (negReal (constantReal zeroRational)))
  | count + 1 =>
      denotesSameRealTrans
        (addRealRespectsDenotesSame
          (sumRealNegReal term count)
          (denotesSameRealRefl (negReal (term count))))
        (denotesSameRealSymm
          (negRealAddRealDenotesSame (sumReal count term) (term count)))

/-! ## Order monotonicity -/

/-- **The sum is monotone** — a per-term `LessEqualReal` on the summed range
lifts to the prefix sums.  Structural induction on the count: the empty sum is
reflexive; the successor step chains the inductive-hypothesis bound (shared
summand `leftTerm count` on the right) with the new-term bound (shared summand
`sumReal count rightTerm` on the left) through `lessEqualRealTrans`. -/
theorem sumRealMonotone {leftTerm rightTerm : Nat → RegularReal} (count : Nat)
    (pointwiseBelow : ∀ position, position < count →
      LessEqualReal (leftTerm position) (rightTerm position)) :
    LessEqualReal (sumReal count leftTerm) (sumReal count rightTerm) :=
  match count with
  | 0 => lessEqualRealRefl (constantReal zeroRational)
  | count + 1 =>
      lessEqualRealTrans
        (lessEqualRealAddCompat
          (sumRealMonotone count
            (fun position isBelow =>
              pointwiseBelow position (Nat.lt_succ_of_lt isBelow)))
          (leftTerm count))
        (lessEqualRealAddCompatLeft (sumReal count rightTerm)
          (pointwiseBelow count (Nat.lt_succ_self count)))

/-! ## The count-scaled rational bound -/

/-- **The count-scaled rational** — `count` copies of `bound` added,
predecessor-shaped so the inductive bound step is definitional. -/
def natScaleRational (count : Nat) (bound : RationalPair) : RationalPair :=
  match count with
  | 0 => zeroRational
  | count + 1 => addExact (natScaleRational count bound) bound

/-- **The sum respects the real-level bound** — a uniform per-term bound `q`
lifts to the `count`-scaled bound.  Each appended pair rides
`addRealRespectsIsWithinRealBound`, and the scaled bound grows by exactly `q`. -/
theorem sumRealRespectsIsWithinRealBound {leftTerm rightTerm : Nat → RegularReal}
    {bound : RationalPair}
    (termsWithin : ∀ position,
      IsWithinRealBound (leftTerm position) (rightTerm position) bound)
    (count : Nat) :
    IsWithinRealBound (sumReal count leftTerm) (sumReal count rightTerm)
      (natScaleRational count bound) :=
  match count with
  | 0 =>
      isWithinRealBoundOfDenotesSameReal
        (denotesSameRealRefl (constantReal zeroRational))
        (lessEqualAsRefl zeroRational)
  | count + 1 =>
      addRealRespectsIsWithinRealBound
        (sumRealRespectsIsWithinRealBound termsWithin count)
        (termsWithin count)

/-! ## The cut split -/

/-- **The sum splits at a cut point** — summing `m + n` terms denotes summing the
first `m` plus summing the next `n` (shifted by `m`).  Induction on the tail
length `n`, closing each step by associativity. -/
theorem sumRealSplit (prefixCount tailCount : Nat) (term : Nat → RegularReal) :
    DenotesSameReal
      (sumReal (prefixCount + tailCount) term)
      (addReal (sumReal prefixCount term)
        (sumReal tailCount (fun position => term (prefixCount + position)))) :=
  match tailCount with
  | 0 =>
      denotesSameRealSymm (addRealZeroRight (sumReal prefixCount term))
  | tailCount + 1 =>
      denotesSameRealTrans
        (addRealRespectsDenotesSame
          (sumRealSplit prefixCount tailCount term)
          (denotesSameRealRefl (term (prefixCount + tailCount))))
        (addRealAssoc (sumReal prefixCount term)
          (sumReal tailCount (fun position => term (prefixCount + position)))
          (term (prefixCount + tailCount)))

/-! ## The block regroup -/

/-- **The product reindex** — summing `blockSize * blockCount` terms denotes the
outer sum over `blockCount` blocks, each an inner sum of `blockSize` terms at
`blockSize * blockIndex + innerIndex`.  The count `blockSize * blockCount` puts
the `Nat.mul` recursion on the block count, so `blockSize * (blockCount + 1)`
reduces DEFINITIONALLY to `blockSize * blockCount + blockSize` and the step is a
single cut split. -/
theorem sumRealRegroupProduct (blockSize blockCount : Nat)
    (term : Nat → RegularReal) :
    DenotesSameReal
      (sumReal (blockSize * blockCount) term)
      (sumReal blockCount
        (fun blockIndex =>
          sumReal blockSize
            (fun innerIndex => term (blockSize * blockIndex + innerIndex)))) :=
  match blockCount with
  | 0 => denotesSameRealRefl (constantReal zeroRational)
  | blockCount + 1 =>
      denotesSameRealTrans
        (sumRealSplit (blockSize * blockCount) blockSize term)
        (addRealRespectsDenotesSame
          (sumRealRegroupProduct blockSize blockCount term)
          (denotesSameRealRefl
            (sumReal blockSize
              (fun innerIndex => term (blockSize * blockCount + innerIndex)))))

/-! ## The finite triangle inequality -/

/-- **The finite triangle inequality** `|Σ term| ≤ Σ |term|` — the absolute value
of a prefix sum is bounded by the prefix sum of the absolute values.  Structural
induction on the count: the empty sum collapses `|0| ~ 0`
(`absRealOfNonNegDenotesSame`); the successor step chains the two-term
subadditivity `|Σ_count + term_count| ≤ |Σ_count| + |term_count|`
(`absRealSubAdditive`) with the inductive bound lifted by the shared summand
`|term_count|` (`lessEqualRealAddCompat`).  The order half of the integral
triangle inequality toward Bishop-L1. -/
theorem sumRealTriangle (term : Nat → RegularReal) (count : Nat) :
    LessEqualReal (absReal (sumReal count term))
      (sumReal count (fun position => absReal (term position))) :=
  match count with
  | 0 =>
      lessEqualRealRespectsDenotesSame
        (denotesSameRealSymm
          (absRealOfNonNegDenotesSame
            (constantRealIsNonNegativeRealOfNonNegative zeroRationalIsNonNegative)))
        (denotesSameRealRefl (constantReal zeroRational))
        (lessEqualRealRefl (constantReal zeroRational))
  | count + 1 =>
      lessEqualRealTrans
        (absRealSubAdditive (sumReal count term) (term count))
        (lessEqualRealAddCompat (sumRealTriangle term count) (absReal (term count)))

end FX1Poly.ComputerAlgebra
