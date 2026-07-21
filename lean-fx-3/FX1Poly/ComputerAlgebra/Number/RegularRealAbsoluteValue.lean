import FX1Poly.ComputerAlgebra.Number.ComplexRealTriangleInequality

/-! # RegularRealAbsoluteValue — the real absolute value `|x| = √(x²)`

The number tower's real absolute value on the zero-axiom Bishop-real setoid,
built as the constructive square root of the square: `absReal x = √(x²)`.  The
nonnegative-radicand witness is `mulRealSelfIsNonNegativeReal` (a real square is
pointwise a rational square), so `absReal` reuses the entire
square-root/order/triangle-inequality stack with no new analytic content.

Everything is a corollary of the square-root order layer:

* `absRealNonNegative`   — `√` is pointwise nonnegative;
* `selfLeAbsReal`        — `x ≤ √(x²)` is exactly `selfLeSqrtRealSquare`;
* `negSelfLeAbsReal`     — `-x ≤ |x|`, transporting `-x ≤ √((-x)²)` across the
                           sign-blind square `(-x)² ~ x²`;
* `absRealRespectsDenotesSame` — setoid congruence, from `mulReal` and `sqrtReal`
                           each respecting the setoid;
* `absRealSubAdditive`   — the real triangle inequality `|x + y| ≤ |x| + |y|`,
                           the 1-D specialisation of `modulusTriangleInequality`:
                           both sides nonnegative, compare squares
                           (`nonNegSquareOrderReflect`), binomial-expand each
                           (`squareSumExpand`), and the single product bound
                           `x·y ≤ |x|·|y|` (`selfLeAbsReal` on `x·y` composed with
                           the multiplicative root) lifts the shared `x² + y²`
                           prefix through `lessEqualRealAddCompatLeft`.

The product bound `x·y ≤ |x|·|y|` is the real Cauchy–Schwarz: `x·y ≤ √((x·y)²) ~
√(x²·y²) ~ √(x²)·√(y²) = |x|·|y|`, the middle step by the multiplicative medial
and `sqrtRealMulDenotesSame`.

Zero-axiom: every declaration is a term-mode composition of the square-root and
real-order lemmas; per-declaration gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-- **The real absolute value** `|x| = √(x²)` — the constructive square root of
the real square, whose nonnegative-radicand witness is
`mulRealSelfIsNonNegativeReal`. -/
def absReal (value : RegularReal) : RegularReal :=
  sqrtReal (mulReal value value) (mulRealSelfIsNonNegativeReal value)

/-- **The absolute value is pointwise nonnegative** — `√` of any nonnegative
radicand is pointwise nonnegative (the STRONG `IsNonNegativeReal`, free from the
square-root construction). -/
theorem absRealNonNegative (value : RegularReal) :
    IsNonNegativeReal (absReal value) :=
  sqrtRealIsNonNegativeReal (mulReal value value)
    (mulRealSelfIsNonNegativeReal value)

/-- **`x ≤ |x|`** — definitionally `x ≤ √(x²)`. -/
theorem selfLeAbsReal (value : RegularReal) :
    LessEqualReal value (absReal value) :=
  selfLeSqrtRealSquare value

/-- **`-x ≤ |x|`** — apply `x ≤ √(x²)` to `-x`, giving `-x ≤ √((-x)²)`, then
transport the right endpoint across the sign-blind square `(-x)² ~ x²`, so
`√((-x)²) ~ √(x²) = |x|`. -/
theorem negSelfLeAbsReal (value : RegularReal) :
    LessEqualReal (negReal value) (absReal value) :=
  lessEqualRealCongr (denotesSameRealRefl (negReal value))
    (sqrtRealRespectsDenotesSame
      (mulRealSelfIsNonNegativeReal (negReal value))
      (mulRealSelfIsNonNegativeReal value)
      (mulRealNegNegDenotesSame value))
    (selfLeSqrtRealSquare (negReal value))

/-- **Setoid congruence** — same-real arguments give same-real absolute values.
The square respects the setoid (`mulReal`), and so does its square root
(`sqrtReal`). -/
theorem absRealRespectsDenotesSame {leftValue rightValue : RegularReal}
    (areSame : DenotesSameReal leftValue rightValue) :
    DenotesSameReal (absReal leftValue) (absReal rightValue) :=
  sqrtRealRespectsDenotesSame
    (mulRealSelfIsNonNegativeReal leftValue)
    (mulRealSelfIsNonNegativeReal rightValue)
    (mulRealRespectsDenotesSame areSame areSame)

/-- **The real triangle inequality** `|x + y| ≤ |x| + |y|` on the Bishop-real
setoid — the 1-D specialisation of `modulusTriangleInequality`.  Both sides are
nonnegative, so it suffices to compare squares (`nonNegSquareOrderReflect`).
Binomial expansion gives `|x + y|² ~ (x² + y²) + (xy + xy)` and `(|x| + |y|)² ~
(x² + y²) + (|x||y| + |x||y|)` (`sqrtRealSquareDenotesSame` collapses
`|x|² ~ x²`), and the product bound `x·y ≤ |x|·|y|` lifts the shared `x² + y²`
prefix through `lessEqualRealAddCompatLeft` to `|x + y|² ≤ (|x| + |y|)²`. -/
theorem absRealSubAdditive (leftValue rightValue : RegularReal) :
    LessEqualReal (absReal (addReal leftValue rightValue))
      (addReal (absReal leftValue) (absReal rightValue)) :=
  let sumValue := addReal leftValue rightValue
  let absSum := absReal sumValue
  let absLeft := absReal leftValue
  let absRight := absReal rightValue
  let squareSumBase :=
    addReal (mulReal leftValue leftValue) (mulReal rightValue rightValue)
  have productBelowAbsProduct :
      LessEqualReal (mulReal leftValue rightValue) (mulReal absLeft absRight) :=
    let radicandSeparated :=
      mulReal (mulReal leftValue leftValue) (mulReal rightValue rightValue)
    have isSeparatedNonNegative : IsNonNegativeReal radicandSeparated :=
      mulRealPreservesIsNonNegativeReal
        (mulRealSelfIsNonNegativeReal leftValue)
        (mulRealSelfIsNonNegativeReal rightValue)
    have absProductDenotesSeparatedRoot :
        DenotesSameReal (absReal (mulReal leftValue rightValue))
          (mulReal absLeft absRight) :=
      denotesSameRealTrans
        (sqrtRealRespectsDenotesSame
          (mulRealSelfIsNonNegativeReal (mulReal leftValue rightValue))
          isSeparatedNonNegative
          (mulRealMedial leftValue rightValue leftValue rightValue))
        (sqrtRealMulDenotesSame
          (mulRealSelfIsNonNegativeReal leftValue)
          (mulRealSelfIsNonNegativeReal rightValue)
          isSeparatedNonNegative)
    lessEqualRealCongr (denotesSameRealRefl (mulReal leftValue rightValue))
      absProductDenotesSeparatedRoot
      (selfLeAbsReal (mulReal leftValue rightValue))
  have doubledProductBelow :
      LessEqualReal
        (addReal (mulReal leftValue rightValue) (mulReal leftValue rightValue))
        (addReal (mulReal absLeft absRight) (mulReal absLeft absRight)) :=
    lessEqualRealTrans
      (lessEqualRealAddCompat productBelowAbsProduct
        (mulReal leftValue rightValue))
      (lessEqualRealAddCompatLeft (mulReal absLeft absRight)
        productBelowAbsProduct)
  have expandedBelow :
      LessEqualReal
        (addReal squareSumBase
          (addReal (mulReal leftValue rightValue) (mulReal leftValue rightValue)))
        (addReal squareSumBase
          (addReal (mulReal absLeft absRight) (mulReal absLeft absRight))) :=
    lessEqualRealAddCompatLeft squareSumBase doubledProductBelow
  have leftSquareExpand :
      DenotesSameReal (mulReal absSum absSum)
        (addReal squareSumBase
          (addReal (mulReal leftValue rightValue)
            (mulReal leftValue rightValue))) :=
    denotesSameRealTrans
      (sqrtRealSquareDenotesSame (mulRealSelfIsNonNegativeReal sumValue))
      (squareSumExpand leftValue rightValue)
  have rightSquareExpand :
      DenotesSameReal
        (mulReal (addReal absLeft absRight) (addReal absLeft absRight))
        (addReal squareSumBase
          (addReal (mulReal absLeft absRight) (mulReal absLeft absRight))) :=
    denotesSameRealTrans
      (squareSumExpand absLeft absRight)
      (addRealRespectsDenotesSame
        (addRealRespectsDenotesSame
          (sqrtRealSquareDenotesSame (mulRealSelfIsNonNegativeReal leftValue))
          (sqrtRealSquareDenotesSame (mulRealSelfIsNonNegativeReal rightValue)))
        (denotesSameRealRefl
          (addReal (mulReal absLeft absRight) (mulReal absLeft absRight))))
  have squaresOrdered :
      LessEqualReal (mulReal absSum absSum)
        (mulReal (addReal absLeft absRight) (addReal absLeft absRight)) :=
    lessEqualRealCongr (denotesSameRealSymm leftSquareExpand)
      (denotesSameRealSymm rightSquareExpand) expandedBelow
  nonNegSquareOrderReflect
    (absRealNonNegative sumValue)
    (addRealPreservesIsNonNegativeReal (absRealNonNegative leftValue)
      (absRealNonNegative rightValue))
    squaresOrdered

/-- **The absolute value is sign-blind** — `|−x| ~ |x|`, transporting the
sign-blind square `(−x)² ~ x²` through the square root's setoid congruence. -/
theorem absRealNegReal (value : RegularReal) :
    DenotesSameReal (absReal (negReal value)) (absReal value) :=
  sqrtRealRespectsDenotesSame
    (mulRealSelfIsNonNegativeReal (negReal value))
    (mulRealSelfIsNonNegativeReal value)
    (mulRealNegNegDenotesSame value)

/-- **The reverse triangle inequality** `|x − y| ≤ |x| + |y|` — the subadditivity
of `|x + (−y)|` (definitionally `|x − y|`) with the sign-blind `|−y| ~ |y|` folded
into the right endpoint. -/
theorem absRealReverseTriangle (leftValue rightValue : RegularReal) :
    LessEqualReal (absReal (subReal leftValue rightValue))
      (addReal (absReal leftValue) (absReal rightValue)) :=
  lessEqualRealRespectsDenotesSame
    (denotesSameRealRefl (absReal (subReal leftValue rightValue)))
    (addRealRespectsDenotesSame (denotesSameRealRefl (absReal leftValue))
      (absRealNegReal rightValue))
    (absRealSubAdditive leftValue (negReal rightValue))

/-- The rational zero is nonnegative — its numerator is `0`. -/
theorem zeroRationalIsNonNegative : IsNonNegative zeroRational :=
  isNonNegativeOfNumeratorNonNegative (intZeroLeOfNat 0)

/-- **A nonnegative rational embeds to a pointwise-nonnegative real** — every
constant approximant IS the nonnegative rational. -/
theorem constantRealIsNonNegativeRealOfNonNegative {value : RationalPair}
    (isNonNegative : IsNonNegative value) :
    IsNonNegativeReal (constantReal value) :=
  fun _ => isNonNegative

/-- **`|x| ~ x` on nonnegatives** — both sides are nonnegative, `x ≤ |x|` holds
always, and `|x| ≤ x` reflects the square order `|x|² ~ x² ≤ x²`; antisymmetry
lands the setoid equality. -/
theorem absRealOfNonNegDenotesSame {value : RegularReal}
    (isNonNegativeReal : IsNonNegativeReal value) :
    DenotesSameReal (absReal value) value :=
  denotesSameRealOfLessEqualBoth
    (nonNegSquareOrderReflect (absRealNonNegative value) isNonNegativeReal
      (lessEqualRealRespectsDenotesSame
        (denotesSameRealSymm
          (sqrtRealSquareDenotesSame (mulRealSelfIsNonNegativeReal value)))
        (denotesSameRealRefl (mulReal value value))
        (lessEqualRealRefl (mulReal value value))))
    (selfLeAbsReal value)

/-- **A nonnegative constant scalar pulls through the absolute value** —
`|c · S| ~ c · |S|` when `c ≥ 0`.  Medially regroup `(cS)² ~ c²S²`, split the root
multiplicatively (`√(c²S²) ~ √(c²)·√(S²) = |c|·|S|`), and collapse `|c| ~ c` by
`absRealOfNonNegDenotesSame`.  A mesh-scaling identity for the Riemann-sum
triangle inequality. -/
theorem absRealMulConstantNonNeg {meshValue : RationalPair}
    (isMeshNonNegative : IsNonNegative meshValue) (summand : RegularReal) :
    DenotesSameReal
      (absReal (mulReal (constantReal meshValue) summand))
      (mulReal (constantReal meshValue) (absReal summand)) :=
  let constantFactor := constantReal meshValue
  denotesSameRealTrans
    (denotesSameRealTrans
      (sqrtRealRespectsDenotesSame
        (mulRealSelfIsNonNegativeReal (mulReal constantFactor summand))
        (mulRealPreservesIsNonNegativeReal
          (mulRealSelfIsNonNegativeReal constantFactor)
          (mulRealSelfIsNonNegativeReal summand))
        (mulRealMedial constantFactor summand constantFactor summand))
      (sqrtRealMulDenotesSame
        (mulRealSelfIsNonNegativeReal constantFactor)
        (mulRealSelfIsNonNegativeReal summand)
        (mulRealPreservesIsNonNegativeReal
          (mulRealSelfIsNonNegativeReal constantFactor)
          (mulRealSelfIsNonNegativeReal summand))))
    (mulRealRespectsDenotesSame
      (absRealOfNonNegDenotesSame
        (constantRealIsNonNegativeRealOfNonNegative isMeshNonNegative))
      (denotesSameRealRefl (absReal summand)))

/-- Marker: the number tower carries the real absolute value with its
nonnegativity, self/neg-self bounds, setoid congruence, and subadditivity
(the real triangle inequality). -/
def fxRegularReal_hasRealAbsoluteValue : Bool := true

end FX1Poly.ComputerAlgebra
