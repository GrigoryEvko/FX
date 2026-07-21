import FX1Poly.ComputerAlgebra.Analysis.RealMultiplicativeContinuity
import FX1Poly.ComputerAlgebra.Number.RegularRealRing

/-! # Real derivatives — modulus of differentiability

A function `RegularReal -> RegularReal` has derivative `derivative` at
`point` when, for every null sequence of nonzero increments `increments`
(each carrying an apartness-from-zero witness so the constructive
reciprocal `inverseRealOfApartness` is total), the Newton difference
quotient sequence

    `(function (point + increment) - function point) * (1 / increment)`

converges to `derivative` with an explicit modulus.  This is the
sequential (Heine) framing, on which the sequence laws
`convergesToAddReal`, `convergesToMulReal`, `convergesToScalarMulReal`
act directly.

The difference quotient never forms `1 / increment` from the increment
alone: it consumes the apartness witness through `inverseRealOfApartness`,
so the definition is total, and the Heyting-field law
`mulRealInverseOfApartnessDenotesOne` (`increment * (1/increment) ~ 1`)
supplies the unit for the identity and product rules.

Rules proved here, all zero-axiom:

  * constant `d/dx c = 0` and identity `d/dx x = 1` — each difference-
    quotient term is setoid-equal to the limit, converging at the zero
    modulus;
  * linearity (sum) `(f+g)' = f' + g'` — the cross-pair split plus
    right-distribution regroups the quotient into `DQ_f + DQ_g`;
  * scalar `(c*f)' = c*f'` — left-distribution over subtraction and
    associativity pull the constant out;
  * differentiable implies continuous — `f(x+h) - f(x) = DQ_f * h`, a
    bounded-times-null product vanishing by `convergesToMulReal`;
  * product / Leibniz `(fg)' = f'*g + f*g'` — the telescope
    `f(x+h)g(x+h) - f(x)g(x) = (f(x+h)-f(x))g(x+h) + f(x)(g(x+h)-g(x))`
    divided by `h` gives `DQ_f * g(x+h) + f(x) * DQ_g`.

The real-level transport tool is the left-slot congruence
`isWithinRealBoundCongrLeftDenotesSameReal`, a distance transitivity
carrying a convergence across a pointwise-setoid-equal reshaping. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## Real-level distance congruence -/

/-- Left-slot congruence of the real-level bound under the setoid: a
setoid-equal replacement in the left slot preserves an `IsWithinRealBound`.
The per-index slack skeleton chains
`newLeft(index) -> newLeft(slack) -> left(slack) -> right(slack) -> right(index)`
through two regularities, the setoid hypothesis (pure `2/(slack+1)`), and the
bound hypothesis (`q + 2/(slack+1)`); the accumulated bound reshapes (pull the
non-vanishing `q` to the front with `addExactSwapOuterIntoInner`, collapse the
remaining four reciprocal legs by `regularityChainBoundCollapses`) onto
`(q + 2/(index+1)) + 6/(slack+1)`, whose nat-numerator slack closes. -/
theorem isWithinRealBoundCongrLeftDenotesSameReal
    {leftValue newLeftValue rightValue : RegularReal} {bound : RationalPair}
    (leftAgrees : DenotesSameReal newLeftValue leftValue)
    (isWithin : IsWithinRealBound leftValue rightValue bound) :
    IsWithinRealBound newLeftValue rightValue bound :=
  fun index =>
    isWithinBoundOfForallSlack (slackNumerator := 6) (fun slackIndex =>
      isWithinBoundCongrBound
        (denotesSameAsTrans
          (addExactRespectsDenotesSameAs
            (denotesSameAsRefl
              (addExact
                (addExact (reciprocalOfSucc index) (reciprocalOfSucc slackIndex))
                (ratioOfNatSucc 2 slackIndex)))
            (addExactAssoc bound (ratioOfNatSucc 2 slackIndex)
              (addExact (reciprocalOfSucc slackIndex) (reciprocalOfSucc index))))
          (denotesSameAsTrans
            (addExactSwapOuterIntoInner
              (addExact
                (addExact (reciprocalOfSucc index) (reciprocalOfSucc slackIndex))
                (ratioOfNatSucc 2 slackIndex))
              bound
              (addExact (ratioOfNatSucc 2 slackIndex)
                (addExact (reciprocalOfSucc slackIndex) (reciprocalOfSucc index))))
            (denotesSameAsTrans
              (addExactRespectsDenotesSameAs (denotesSameAsRefl bound)
                (regularityChainBoundCollapses index slackIndex))
              (denotesSameAsSymm
                (addExactAssoc bound (ratioOfNatSucc 2 index)
                  (ratioOfNatSucc 6 slackIndex))))))
        (isWithinBoundTriangle
          (isWithinBoundTriangle
            (newLeftValue.isRegular index slackIndex)
            (leftAgrees slackIndex))
          (isWithinBoundTriangle
            (isWithin slackIndex)
            (rightValue.isRegular slackIndex index))))

/-- Right-slot congruence: via symmetry, replace the limit slot with a
setoid-equal real. -/
theorem isWithinRealBoundCongrRightDenotesSameReal
    {leftValue rightValue newRightValue : RegularReal} {bound : RationalPair}
    (rightAgrees : DenotesSameReal newRightValue rightValue)
    (isWithin : IsWithinRealBound leftValue rightValue bound) :
    IsWithinRealBound leftValue newRightValue bound :=
  isWithinRealBoundSymm
    (isWithinRealBoundCongrLeftDenotesSameReal rightAgrees
      (isWithinRealBoundSymm isWithin))

/-! ## Convergence transport across setoid reshaping -/

/-- Convergence transports across a pointwise-setoid-equal reshaping: if
`sequence position` is setoid-equal to `otherSequence position` at every
position and the latter converges, so does the former, with the same modulus. -/
theorem convergesToOfPointwiseDenotesSameReal
    {sequence otherSequence : Nat → RegularReal} {limit : RegularReal}
    {modulus : Nat → Nat}
    (pointwiseAgree :
      ∀ position, DenotesSameReal (sequence position) (otherSequence position))
    (convergesOther : ConvergesTo otherSequence limit modulus) :
    ConvergesTo sequence limit modulus :=
  fun precisionIndex position isReached =>
    isWithinRealBoundCongrLeftDenotesSameReal (pointwiseAgree position)
      (convergesOther precisionIndex position isReached)

/-- Convergence transports across a setoid-equal limit: a setoid-equal
limit is reached by the same sequence with the same modulus. -/
theorem convergesToCongrLimitDenotesSameReal
    {sequence : Nat → RegularReal} {limit newLimit : RegularReal}
    {modulus : Nat → Nat}
    (limitAgrees : DenotesSameReal limit newLimit)
    (converges : ConvergesTo sequence limit modulus) :
    ConvergesTo sequence newLimit modulus :=
  fun precisionIndex position isReached =>
    isWithinRealBoundCongrRightDenotesSameReal (denotesSameRealSymm limitAgrees)
      (converges precisionIndex position isReached)

/-! ## Ring reshaping shims for the difference quotients -/

/-- Negation is a left inverse for addition: commute onto the
right-inverse law. -/
theorem addRealNegLeft (value : RegularReal) :
    DenotesSameReal (addReal (negReal value) value) (constantReal zeroRational) :=
  denotesSameRealTrans (addRealComm (negReal value) value) (addRealNegRight value)

/-- Add-then-subtract cancels: `(point + perturbation) - point` denotes
`perturbation` — commute the sum, associate the cancelling pair, drop zero. -/
theorem subRealAddPerturbationDenotesSame (point perturbation : RegularReal) :
    DenotesSameReal (subReal (addReal point perturbation) point) perturbation :=
  denotesSameRealTrans
    (addRealRespectsDenotesSame (addRealComm point perturbation)
      (denotesSameRealRefl (negReal point)))
    (denotesSameRealTrans
      (addRealAssoc perturbation point (negReal point))
      (denotesSameRealTrans
        (addRealRespectsDenotesSame (denotesSameRealRefl perturbation)
          (addRealNegRight point))
        (addRealZeroRight perturbation)))

/-- Subtract-then-add restores: `(value - base) + base` denotes `value` —
associate the cancelling pair, drop zero. -/
theorem addRealSubRealBaseDenotesSame (value base : RegularReal) :
    DenotesSameReal (addReal (subReal value base) base) value :=
  denotesSameRealTrans
    (addRealAssoc value (negReal base) base)
    (denotesSameRealTrans
      (addRealRespectsDenotesSame (denotesSameRealRefl value) (addRealNegLeft base))
      (addRealZeroRight value))

/-- The three-point telescope: `(first - middle) + (middle - last)` denotes
`first - last` — associate onto the cancelling `(-middle) + middle`. -/
theorem addRealSubRealTelescopeDenotesSame
    (firstValue middleValue lastValue : RegularReal) :
    DenotesSameReal
      (addReal (subReal firstValue middleValue) (subReal middleValue lastValue))
      (subReal firstValue lastValue) :=
  denotesSameRealTrans
    (addRealAssoc firstValue (negReal middleValue)
      (addReal middleValue (negReal lastValue)))
    (addRealRespectsDenotesSame (denotesSameRealRefl firstValue)
      (denotesSameRealTrans
        (denotesSameRealSymm
          (addRealAssoc (negReal middleValue) middleValue (negReal lastValue)))
        (denotesSameRealTrans
          (addRealRespectsDenotesSame (addRealNegLeft middleValue)
            (denotesSameRealRefl (negReal lastValue)))
          (addRealZeroLeft (negReal lastValue)))))

/-- The product telescope at the real level:
`(a*c) - (b*d)` denotes `(a-b)*c + b*(c-d)`, the Leibniz split.  Push each
product-difference leg through distributivity, then the three-point telescope
on `a*c, b*c, b*d`. -/
theorem subRealMulTelescopeDenotesSame
    (leftNew leftOld rightNew rightOld : RegularReal) :
    DenotesSameReal
      (subReal (mulReal leftNew rightNew) (mulReal leftOld rightOld))
      (addReal (mulReal (subReal leftNew leftOld) rightNew)
        (mulReal leftOld (subReal rightNew rightOld))) :=
  denotesSameRealSymm
    (denotesSameRealTrans
      (addRealRespectsDenotesSame
        (mulRealSubRealRightDenotesSame leftNew leftOld rightNew)
        (mulRealSubRealDenotesSame leftOld rightNew rightOld))
      (addRealSubRealTelescopeDenotesSame (mulReal leftNew rightNew)
        (mulReal leftOld rightNew) (mulReal leftOld rightOld)))

/-! ## The difference quotient -/

/-- The Newton difference quotient at a nonzero perturbation:
`(function (point + perturbation) - function point) * (1 / perturbation)`.
The reciprocal is the apartness-first constructive inverse, consuming exactly
the `perturbation != 0` datum, so the quotient is total. -/
def differenceQuotient (function : RegularReal → RegularReal)
    (point perturbation : RegularReal)
    (isApartFromZero : RealApartnessWitness perturbation (constantReal zeroRational)) :
    RegularReal :=
  mulReal
    (subReal (function (addReal point perturbation)) (function point))
    (inverseRealOfApartness isApartFromZero)

/-! ## The derivative predicate -/

/-- The difference-quotient sequence converges, for one null increment
sequence: bundles the explicit quotient modulus with the convergence. -/
structure DifferenceQuotientConverges (function : RegularReal → RegularReal)
    (point derivative : RegularReal) (increments : Nat → RegularReal)
    (apartnessWitnesses :
      ∀ position,
        RealApartnessWitness (increments position) (constantReal zeroRational)) :
    Type where
  quotientModulus : Nat → Nat
  convergesToDerivative :
    ConvergesTo
      (fun position =>
        differenceQuotient function point (increments position)
          (apartnessWitnesses position))
      derivative quotientModulus

/-- Has derivative at a point: for every null sequence of nonzero
increments, the difference-quotient sequence converges to `derivative`.
`Type`-valued because the per-sequence quotient modulus is constructive data,
like `RegularReal`'s approximation and the `Type`-valued apartness witness. -/
def HasDerivativeAt (function : RegularReal → RegularReal)
    (point derivative : RegularReal) : Type :=
  ∀ (increments : Nat → RegularReal)
    (apartnessWitnesses :
      ∀ position,
        RealApartnessWitness (increments position) (constantReal zeroRational))
    (nullModulus : Nat → Nat),
    ConvergesTo increments (constantReal zeroRational) nullModulus →
      DifferenceQuotientConverges function point derivative increments
        apartnessWitnesses

/-! ## Constant and identity derivatives -/

/-- The derivative of a constant is zero.  Each quotient term is
`(c - c) * (1/h) ~ 0 * (1/h) ~ 0`, setoid-constantly the limit. -/
def hasDerivativeAtConstant (constantValue point : RegularReal) :
    HasDerivativeAt (fun _ => constantValue) point (constantReal zeroRational) :=
  fun increments apartnessWitnesses _ _ =>
    ⟨fun _ => 0,
      convergesToOfPointwiseDenotesSameReal
        (fun position =>
          denotesSameRealTrans
            (mulRealRespectsDenotesSame (addRealNegRight constantValue)
              (denotesSameRealRefl
                (inverseRealOfApartness (apartnessWitnesses position))))
            (mulRealZeroLeft
              (inverseRealOfApartness (apartnessWitnesses position))))
        (convergesToConstant (constantReal zeroRational))⟩

/-- The derivative of the identity is one.  Each quotient term is
`((x + h) - x) * (1/h) ~ h * (1/h) ~ 1`, setoid-constantly the limit. -/
def hasDerivativeAtIdentity (point : RegularReal) :
    HasDerivativeAt (fun value => value) point (constantReal oneRational) :=
  fun increments apartnessWitnesses _ _ =>
    ⟨fun _ => 0,
      convergesToOfPointwiseDenotesSameReal
        (fun position =>
          denotesSameRealTrans
            (mulRealRespectsDenotesSame
              (subRealAddPerturbationDenotesSame point (increments position))
              (denotesSameRealRefl
                (inverseRealOfApartness (apartnessWitnesses position))))
            (mulRealInverseOfApartnessDenotesOne (apartnessWitnesses position)))
        (convergesToConstant (constantReal oneRational))⟩

/-! ## Linearity (sum rule) -/

/-- The sum rule `(f + g)' = f' + g'`.  The cross-pair split regroups the
sum's difference quotient into `DQ_f + DQ_g`, then `convergesToAddReal`. -/
def hasDerivativeAtAddReal {function otherFunction : RegularReal → RegularReal}
    {point derivative otherDerivative : RegularReal}
    (hasDeriv : HasDerivativeAt function point derivative)
    (hasOtherDeriv : HasDerivativeAt otherFunction point otherDerivative) :
    HasDerivativeAt (fun value => addReal (function value) (otherFunction value))
      point (addReal derivative otherDerivative) :=
  fun increments apartnessWitnesses nullModulus isNull =>
    let quotientOfFunction :=
      hasDeriv increments apartnessWitnesses nullModulus isNull
    let quotientOfOther :=
      hasOtherDeriv increments apartnessWitnesses nullModulus isNull
    ⟨_,
      convergesToOfPointwiseDenotesSameReal
        (fun position =>
          denotesSameRealTrans
            (mulRealRespectsDenotesSame
              (subRealCrossPairsDenotesSame
                (function (addReal point (increments position)))
                (otherFunction (addReal point (increments position)))
                (function point) (otherFunction point))
              (denotesSameRealRefl
                (inverseRealOfApartness (apartnessWitnesses position))))
            (mulRealRightDistrib
              (subReal (function (addReal point (increments position)))
                (function point))
              (subReal (otherFunction (addReal point (increments position)))
                (otherFunction point))
              (inverseRealOfApartness (apartnessWitnesses position))))
        (convergesToAddReal quotientOfFunction.convergesToDerivative
          quotientOfOther.convergesToDerivative)⟩

/-! ## Scalar rule -/

/-- The scalar rule `(c * f)' = c * f'` for a fixed real factor `c`.
Left-distribution over subtraction and associativity pull the factor out of the
quotient, then `convergesToScalarMulReal`. -/
def hasDerivativeAtScalarMulReal {function : RegularReal → RegularReal}
    {point derivative : RegularReal} (factor : RegularReal)
    (hasDeriv : HasDerivativeAt function point derivative) :
    HasDerivativeAt (fun value => mulReal factor (function value)) point
      (mulReal factor derivative) :=
  fun increments apartnessWitnesses nullModulus isNull =>
    let quotientOfFunction :=
      hasDeriv increments apartnessWitnesses nullModulus isNull
    ⟨_,
      convergesToOfPointwiseDenotesSameReal
        (fun position =>
          denotesSameRealTrans
            (mulRealRespectsDenotesSame
              (denotesSameRealSymm
                (mulRealSubRealDenotesSame factor
                  (function (addReal point (increments position)))
                  (function point)))
              (denotesSameRealRefl
                (inverseRealOfApartness (apartnessWitnesses position))))
            (mulRealAssoc factor
              (subReal (function (addReal point (increments position)))
                (function point))
              (inverseRealOfApartness (apartnessWitnesses position))))
        (convergesToScalarMulReal quotientOfFunction.convergesToDerivative)⟩

/-! ## Differentiable implies continuous -/

/-- The shifted value converges (sequential continuity):
`function (point + increment_n)` converges to `function point`. -/
structure ShiftedValueConverges (function : RegularReal → RegularReal)
    (point : RegularReal) (increments : Nat → RegularReal) : Type where
  shiftModulus : Nat → Nat
  convergesToValue :
    ConvergesTo (fun position => function (addReal point (increments position)))
      (function point) shiftModulus

/-- Differentiable implies continuous (sequential form): at every null
increment sequence, `function (point + increment_n) -> function point`.  The
identity `function (point + h) - function point = DQ_f * h` exhibits the shifted
value as a bounded-convergent quotient times a null increment, so the product
vanishes (`convergesToMulReal`) and adding back `function point` recovers the
value. -/
def differentiableImpliesContinuous {function : RegularReal → RegularReal}
    {point derivative : RegularReal}
    (hasDeriv : HasDerivativeAt function point derivative)
    (increments : Nat → RegularReal)
    (apartnessWitnesses :
      ∀ position,
        RealApartnessWitness (increments position) (constantReal zeroRational))
    (nullModulus : Nat → Nat)
    (isNull : ConvergesTo increments (constantReal zeroRational) nullModulus) :
    ShiftedValueConverges function point increments :=
  let quotientOfFunction :=
    hasDeriv increments apartnessWitnesses nullModulus isNull
  ⟨_,
    convergesToOfPointwiseDenotesSameReal
      (fun position =>
        denotesSameRealSymm
          (denotesSameRealTrans
            (addRealRespectsDenotesSame
              (denotesSameRealTrans
                (mulRealAssoc
                  (subReal (function (addReal point (increments position)))
                    (function point))
                  (inverseRealOfApartness (apartnessWitnesses position))
                  (increments position))
                (denotesSameRealTrans
                  (mulRealRespectsDenotesSame
                    (denotesSameRealRefl
                      (subReal (function (addReal point (increments position)))
                        (function point)))
                    (denotesSameRealTrans
                      (mulRealComm
                        (inverseRealOfApartness (apartnessWitnesses position))
                        (increments position))
                      (mulRealInverseOfApartnessDenotesOne
                        (apartnessWitnesses position))))
                  (mulRealOneRight
                    (subReal (function (addReal point (increments position)))
                      (function point)))))
              (denotesSameRealRefl (function point)))
            (addRealSubRealBaseDenotesSame
              (function (addReal point (increments position))) (function point))))
      (convergesToCongrLimitDenotesSameReal
        (addRealZeroLeft (function point))
        (convergesToAddReal
          (convergesToCongrLimitDenotesSameReal
            (mulRealZeroRight derivative)
            (convergesToMulReal quotientOfFunction.convergesToDerivative isNull))
          (convergesToConstant (function point))))⟩

/-! ## Product rule (Leibniz) -/

/-- The Leibniz reshaping of the product difference quotient: the raw
quotient `((a*c) - (b*d)) * e` denotes `(a-b)*e * c + b * ((c-d)*e)` — the
telescope split, distribution over the reciprocal, and one associativity swap
per term.  With `a,c` the shifted values, `b,d` the base values, `e` the
reciprocal, the right side is `DQ_f * g(x+h) + f(x) * DQ_g`. -/
theorem productDifferenceQuotientDenotesSame
    (shiftedFunctionValue functionValue shiftedOtherValue otherValue
      reciprocal : RegularReal) :
    DenotesSameReal
      (mulReal
        (subReal (mulReal shiftedFunctionValue shiftedOtherValue)
          (mulReal functionValue otherValue))
        reciprocal)
      (addReal
        (mulReal
          (mulReal (subReal shiftedFunctionValue functionValue) reciprocal)
          shiftedOtherValue)
        (mulReal functionValue
          (mulReal (subReal shiftedOtherValue otherValue) reciprocal))) :=
  denotesSameRealTrans
    (mulRealRespectsDenotesSame
      (subRealMulTelescopeDenotesSame shiftedFunctionValue functionValue
        shiftedOtherValue otherValue)
      (denotesSameRealRefl reciprocal))
    (denotesSameRealTrans
      (mulRealRightDistrib
        (mulReal (subReal shiftedFunctionValue functionValue) shiftedOtherValue)
        (mulReal functionValue (subReal shiftedOtherValue otherValue))
        reciprocal)
      (addRealRespectsDenotesSame
        (denotesSameRealTrans
          (mulRealAssoc (subReal shiftedFunctionValue functionValue)
            shiftedOtherValue reciprocal)
          (denotesSameRealTrans
            (mulRealRespectsDenotesSame
              (denotesSameRealRefl (subReal shiftedFunctionValue functionValue))
              (mulRealComm shiftedOtherValue reciprocal))
            (denotesSameRealSymm
              (mulRealAssoc (subReal shiftedFunctionValue functionValue)
                reciprocal shiftedOtherValue))))
        (mulRealAssoc functionValue (subReal shiftedOtherValue otherValue)
          reciprocal)))

/-- The product rule `(f * g)' = f' * g + f * g'`.  The Leibniz telescope
splits the product's difference quotient into `DQ_f * g(x+h) + f(x) * DQ_g`;
the first term rides `convergesToMulReal` against the continuity sub-lemma
(`g(x+h) -> g(x)`, bounded factor absorbed inside `convergesToMulReal`), the
second `convergesToScalarMulReal`, recombined by `convergesToAddReal`. -/
def hasDerivativeAtMulReal {function otherFunction : RegularReal → RegularReal}
    {point derivative otherDerivative : RegularReal}
    (hasDeriv : HasDerivativeAt function point derivative)
    (hasOtherDeriv : HasDerivativeAt otherFunction point otherDerivative) :
    HasDerivativeAt
      (fun value => mulReal (function value) (otherFunction value)) point
      (addReal (mulReal derivative (otherFunction point))
        (mulReal (function point) otherDerivative)) :=
  fun increments apartnessWitnesses nullModulus isNull =>
    let quotientOfFunction :=
      hasDeriv increments apartnessWitnesses nullModulus isNull
    let quotientOfOther :=
      hasOtherDeriv increments apartnessWitnesses nullModulus isNull
    let otherContinuous :=
      differentiableImpliesContinuous hasOtherDeriv increments apartnessWitnesses
        nullModulus isNull
    ⟨_,
      convergesToOfPointwiseDenotesSameReal
        (fun position =>
          productDifferenceQuotientDenotesSame
            (function (addReal point (increments position))) (function point)
            (otherFunction (addReal point (increments position)))
            (otherFunction point)
            (inverseRealOfApartness (apartnessWitnesses position)))
        (convergesToAddReal
          (convergesToMulReal quotientOfFunction.convergesToDerivative
            otherContinuous.convergesToValue)
          (convergesToScalarMulReal quotientOfOther.convergesToDerivative))⟩

end FX1Poly.ComputerAlgebra
