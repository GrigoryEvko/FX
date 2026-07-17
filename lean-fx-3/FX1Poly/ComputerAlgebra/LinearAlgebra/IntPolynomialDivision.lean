import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegree

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialDivision — monic division with remainder
(the third brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

`IntUnivariatePolynomial` shipped the ℤ[x] ring and `IntPolynomialDegree` the degree / leading coefficient
/ normal form.  This file is the division-with-remainder algorithm for a MONIC divisor — the ℤ analog of
monic division over ℚ (over ℚ every nonzero polynomial normalizes to monic, and the characteristic and
minimal polynomials that drive the similarity classifier are already monic).

## The algorithm

`polyDivModMonic fuel divisor dividend` returns `(quotient, remainder)`.  Each step peels off the leading
term: the quotient term is `leadingCoeff(dividend) · x^(deg dividend − deg divisor)`, and the remainder so
far is `dividend − quotientTerm · divisor` (which the leading-term cancellation shrinks).  `fuel` bounds
the recursion structurally.

## What is PROVEN

`polyDivModMonicReconstructs`: for every fuel, `eval_point(dividend) = eval_point(quotient) · eval_point(divisor)
+ eval_point(remainder)` at every point.  Crucially this identity holds REGARDLESS of whether the fuel was
adequate — it rests only on the ring homomorphism (`polyEvalSub`/`polyEvalMul`/`polyEvalAdd`), decoupling
correctness from termination.  The step arithmetic (`D − qt·G = sq·G + Rem ⟹ D = (qt+sq)·G + Rem`) is the
corpus `Int` distributivity/cancellation.

For an ARBITRARY (non-monic) divisor, `polyPseudoDivModReconstructs` gives the subresultant identity
`leadDivisor^scalePower · dividend = quotient · divisor + remainder` — pseudo-division scales the running
dividend by the divisor's leading coefficient each step to stay integral, so the Euclidean GCD runs over ℤ
with no rationals.  The degree bound `deg remainder < deg divisor` (needed for uniqueness and for the
Euclidean GCD's termination) is the honest remaining step, tracked as the next brick.

## Zero-axiom design

The recursion is structural on `fuel`; the only non-list case analysis is `Nat.decLt` (its full
`isTrue`/`isFalse` enumeration).  Every arithmetic step routes through the corpus `Int` lemmas.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialDivision.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## The `Int` cancellation helpers -/

/-- `(minuend − subtrahend) + subtrahend = minuend` over ℤ — subtraction is addition of the negation, so
this is `intSubEqAddNeg` + `intAddLeftNeg` + `intAddZero`. -/
theorem intAddSubCancel (minuend subtrahend : Int) :
    (minuend - subtrahend) + subtrahend = minuend :=
  (congrArg (· + subtrahend) (intSubEqAddNeg minuend subtrahend)).trans
    ((intAddAssoc minuend (-subtrahend) subtrahend).trans
      ((congrArg (minuend + ·) (intAddLeftNeg subtrahend)).trans
        (intAddZero minuend)))

/-- **The division-step reconstruction, at the ℤ level.**  From `D − qt·G = sq·G + Rem` conclude
`D = (qt + sq)·G + Rem` — add `qt·G` back, then re-associate and factor by right distributivity. -/
theorem polyDivStepArith (dividendEval quotientTermEval subQuotientEval divisorEval remainderEval : Int)
    (reducedIdentity :
      dividendEval - quotientTermEval * divisorEval
        = subQuotientEval * divisorEval + remainderEval) :
    dividendEval
      = (quotientTermEval + subQuotientEval) * divisorEval + remainderEval :=
  (intAddSubCancel dividendEval (quotientTermEval * divisorEval)).symm.trans
    ((congrArg (· + quotientTermEval * divisorEval) reducedIdentity).trans
      ((intAddComm (subQuotientEval * divisorEval + remainderEval)
          (quotientTermEval * divisorEval)).trans
        ((intAddAssoc (quotientTermEval * divisorEval) (subQuotientEval * divisorEval) remainderEval).symm.trans
          (congrArg (· + remainderEval)
            (intRightDistrib quotientTermEval subQuotientEval divisorEval).symm))))

/-! ## The monic division algorithm -/

/-- Division with remainder by a monic divisor.  `fuel` bounds the recursion; each step subtracts the
leading-term multiple `quotientTerm · divisor`. -/
def polyDivModMonic : Nat → List Int → List Int → (List Int × List Int)
  | 0, _, dividend => ([], dividend)
  | fuel + 1, divisor, dividend =>
      match Nat.decLt (polyDegree dividend) (polyDegree divisor) with
      | isTrue _ => ([], dividend)
      | isFalse _ =>
          let quotientTerm :=
            polyMonomial (polyLeadingCoeff dividend) (polyDegree dividend - polyDegree divisor)
          let subResult := polyDivModMonic fuel divisor (polySub dividend (polyMul quotientTerm divisor))
          (polyAdd quotientTerm subResult.1, subResult.2)

/-! ## The reconstruction identity (PROVEN, fuel-independent) -/

/-- **Division reconstructs the dividend.**  `eval_point(dividend) = eval_point(quotient) · eval_point(divisor)
+ eval_point(remainder)` for every fuel — the ring-homomorphism identity underlying division, independent
of whether the fuel sufficed. -/
theorem polyDivModMonicReconstructs (point : Int) :
    ∀ (fuel : Nat) (divisor dividend : List Int),
      polyEval point dividend
        = polyEval point (polyDivModMonic fuel divisor dividend).1 * polyEval point divisor
          + polyEval point (polyDivModMonic fuel divisor dividend).2
  | 0, divisor, dividend => by
      show polyEval point dividend
        = polyEval point ([] : List Int) * polyEval point divisor + polyEval point dividend
      exact ((intZeroAdd (polyEval point dividend)).symm.trans
        (congrArg (· + polyEval point dividend) (intZeroMul (polyEval point divisor)).symm))
  | fuel + 1, divisor, dividend => by
      dsimp only [polyDivModMonic]
      cases Nat.decLt (polyDegree dividend) (polyDegree divisor) with
      | isTrue _ =>
          show polyEval point dividend
            = polyEval point ([] : List Int) * polyEval point divisor + polyEval point dividend
          exact ((intZeroAdd (polyEval point dividend)).symm.trans
            (congrArg (· + polyEval point dividend) (intZeroMul (polyEval point divisor)).symm))
      | isFalse _ =>
          have ihStep := polyDivModMonicReconstructs point fuel divisor
            (polySub dividend
              (polyMul (polyMonomial (polyLeadingCoeff dividend)
                (polyDegree dividend - polyDegree divisor)) divisor))
          have reducedIdentity :
              polyEval point dividend
                  - polyEval point
                      (polyMonomial (polyLeadingCoeff dividend)
                        (polyDegree dividend - polyDegree divisor))
                    * polyEval point divisor
                = polyEval point
                    (polyDivModMonic fuel divisor
                      (polySub dividend
                        (polyMul (polyMonomial (polyLeadingCoeff dividend)
                          (polyDegree dividend - polyDegree divisor)) divisor))).1
                  * polyEval point divisor
                  + polyEval point
                    (polyDivModMonic fuel divisor
                      (polySub dividend
                        (polyMul (polyMonomial (polyLeadingCoeff dividend)
                          (polyDegree dividend - polyDegree divisor)) divisor))).2 := by
            refine Eq.trans ?_ ihStep
            exact ((polyEvalSub point dividend
                (polyMul (polyMonomial (polyLeadingCoeff dividend)
                  (polyDegree dividend - polyDegree divisor)) divisor)).trans
              (congrArg (polyEval point dividend - ·)
                (polyEvalMul point (polyMonomial (polyLeadingCoeff dividend)
                  (polyDegree dividend - polyDegree divisor)) divisor))).symm
          refine Eq.trans (polyDivStepArith (polyEval point dividend)
            (polyEval point (polyMonomial (polyLeadingCoeff dividend)
              (polyDegree dividend - polyDegree divisor)))
            (polyEval point
              (polyDivModMonic fuel divisor
                (polySub dividend
                  (polyMul (polyMonomial (polyLeadingCoeff dividend)
                    (polyDegree dividend - polyDegree divisor)) divisor))).1)
            (polyEval point divisor)
            (polyEval point
              (polyDivModMonic fuel divisor
                (polySub dividend
                  (polyMul (polyMonomial (polyLeadingCoeff dividend)
                    (polyDegree dividend - polyDegree divisor)) divisor))).2)
            reducedIdentity) ?_
          exact congrArg
            (· * polyEval point divisor
              + polyEval point
                (polyDivModMonic fuel divisor
                  (polySub dividend
                    (polyMul (polyMonomial (polyLeadingCoeff dividend)
                      (polyDegree dividend - polyDegree divisor)) divisor))).2)
            (polyEvalAdd point
              (polyMonomial (polyLeadingCoeff dividend)
                (polyDegree dividend - polyDegree divisor))
              (polyDivModMonic fuel divisor
                (polySub dividend
                  (polyMul (polyMonomial (polyLeadingCoeff dividend)
                    (polyDegree dividend - polyDegree divisor)) divisor))).1).symm

/-! ## Exact divisibility (division with zero remainder) -/

/-- **Zero remainder means exact division.**  When the remainder trims to the zero polynomial,
`eval_point(dividend) = eval_point(quotient) · eval_point(divisor)` at every point — the monic divisor
divides the dividend.  This is the atomic operation the GCD and factorization steps rest on: it drops the
remainder term of the reconstruction identity once that term is proved to vanish everywhere. -/
theorem polyDividesMonicEvalMultiple (point : Int) (fuel : Nat) (divisor dividend : List Int)
    (remainderTrimsToZero : polyTrim (polyDivModMonic fuel divisor dividend).2 = []) :
    polyEval point dividend
      = polyEval point (polyDivModMonic fuel divisor dividend).1 * polyEval point divisor :=
  (polyDivModMonicReconstructs point fuel divisor dividend).trans
    ((congrArg
        (polyEval point (polyDivModMonic fuel divisor dividend).1 * polyEval point divisor + ·)
        ((polyTrimPreservesEval point (polyDivModMonic fuel divisor dividend).2).symm.trans
          (congrArg (polyEval point) remainderTrimsToZero))).trans
      (intAddZero (polyEval point (polyDivModMonic fuel divisor dividend).1 * polyEval point divisor)))

/-! ## Pseudo-division (arbitrary divisor, ℤ-native)

Monic division needs a leading coefficient of `1`.  For an ARBITRARY divisor with leading coefficient `b`,
pseudo-division stays integral by scaling the running dividend by `b` before each leading-term subtraction.
The reconstruction becomes `b^k · dividend = quotient · divisor + remainder`, where `k` is the number of
reduction steps — the subresultant identity that drives the ℤ-native Euclidean GCD (no rationals needed).
Like the monic case, the identity holds fuel-independently, resting only on the ring homomorphism. -/

/-- `P · (X − Y) = P · X − P · Y` over ℤ — left distributivity over a difference. -/
theorem intMulSubDistrib (scale leftValue rightValue : Int) :
    scale * (leftValue - rightValue) = scale * leftValue - scale * rightValue :=
  (congrArg (scale * ·) (intSubEqAddNeg leftValue rightValue)).trans
    ((intLeftDistrib scale leftValue (-rightValue)).trans
      ((congrArg (scale * leftValue + ·) (intMulNeg scale rightValue)).trans
        (intSubEqAddNeg (scale * leftValue) (scale * rightValue)).symm))

/-- **The pseudo-division-step reconstruction, at the ℤ level.**  From
`P · (b·D − qt·G) = sq·G + Rem` conclude `(P·b)·D = (P·qt + sq)·G + Rem` — distribute the scale, add the
subtracted product back, and factor by right distributivity. -/
theorem polyPseudoDivStepArith
    (scalePower dividendEval quotientTermEval subQuotientEval divisorEval subRemainderEval leadDivisor : Int)
    (reducedIdentity :
      scalePower * (leadDivisor * dividendEval - quotientTermEval * divisorEval)
        = subQuotientEval * divisorEval + subRemainderEval) :
    (scalePower * leadDivisor) * dividendEval
      = (scalePower * quotientTermEval + subQuotientEval) * divisorEval + subRemainderEval :=
  calc (scalePower * leadDivisor) * dividendEval
      = scalePower * (leadDivisor * dividendEval) :=
        intMulAssoc scalePower leadDivisor dividendEval
    _ = (scalePower * (leadDivisor * dividendEval)
            - scalePower * (quotientTermEval * divisorEval))
          + scalePower * (quotientTermEval * divisorEval) :=
        (intAddSubCancel (scalePower * (leadDivisor * dividendEval))
          (scalePower * (quotientTermEval * divisorEval))).symm
    _ = (subQuotientEval * divisorEval + subRemainderEval)
          + scalePower * (quotientTermEval * divisorEval) :=
        congrArg (· + scalePower * (quotientTermEval * divisorEval))
          ((intMulSubDistrib scalePower (leadDivisor * dividendEval)
            (quotientTermEval * divisorEval)).symm.trans reducedIdentity)
    _ = scalePower * (quotientTermEval * divisorEval)
          + (subQuotientEval * divisorEval + subRemainderEval) :=
        intAddComm (subQuotientEval * divisorEval + subRemainderEval)
          (scalePower * (quotientTermEval * divisorEval))
    _ = (scalePower * (quotientTermEval * divisorEval) + subQuotientEval * divisorEval)
          + subRemainderEval :=
        (intAddAssoc (scalePower * (quotientTermEval * divisorEval))
          (subQuotientEval * divisorEval) subRemainderEval).symm
    _ = ((scalePower * quotientTermEval) * divisorEval + subQuotientEval * divisorEval)
          + subRemainderEval :=
        congrArg (fun leadingProduct => (leadingProduct + subQuotientEval * divisorEval) + subRemainderEval)
          (intMulAssoc scalePower quotientTermEval divisorEval).symm
    _ = (scalePower * quotientTermEval + subQuotientEval) * divisorEval + subRemainderEval :=
        congrArg (· + subRemainderEval)
          (intRightDistrib (scalePower * quotientTermEval) subQuotientEval divisorEval).symm

/-- Pseudo-division with remainder by an arbitrary divisor.  Returns `(scalePower, quotient, remainder)`
with the invariant `leadDivisor^scalePower · dividend = quotient · divisor + remainder`.  Each step scales
the running dividend by the divisor's leading coefficient before the leading-term subtraction, keeping
everything integral, and re-scales the accumulated quotient by the divisor's leading coefficient. -/
def polyPseudoDivMod : Nat → List Int → List Int → (Nat × List Int × List Int)
  | 0, _, dividend => (0, [], dividend)
  | fuel + 1, divisor, dividend =>
      match Nat.decLt (polyDegree dividend) (polyDegree divisor) with
      | isTrue _ => (0, [], dividend)
      | isFalse _ =>
          let leadDivisor := polyLeadingCoeff divisor
          let quotientTerm :=
            polyMonomial (polyLeadingCoeff dividend) (polyDegree dividend - polyDegree divisor)
          let subResult :=
            polyPseudoDivMod fuel divisor
              (polySub (polyScale leadDivisor dividend) (polyMul quotientTerm divisor))
          (subResult.1 + 1,
           polyAdd (polyScale (intPower leadDivisor subResult.1) quotientTerm) subResult.2.1,
           subResult.2.2)

/-- **Pseudo-division reconstructs the scaled dividend.**  `leadDivisor^scalePower · eval_point(dividend) =
eval_point(quotient) · eval_point(divisor) + eval_point(remainder)` for every fuel — the subresultant
identity, again fuel-independent (rests only on the ring homomorphism and `intPower`). -/
theorem polyPseudoDivModReconstructs (point : Int) :
    ∀ (fuel : Nat) (divisor dividend : List Int),
      intPower (polyLeadingCoeff divisor) (polyPseudoDivMod fuel divisor dividend).1
          * polyEval point dividend
        = polyEval point (polyPseudoDivMod fuel divisor dividend).2.1 * polyEval point divisor
          + polyEval point (polyPseudoDivMod fuel divisor dividend).2.2
  | 0, divisor, dividend => by
      show intPower (polyLeadingCoeff divisor) 0 * polyEval point dividend
        = polyEval point ([] : List Int) * polyEval point divisor + polyEval point dividend
      exact (intOneMul (polyEval point dividend)).trans
        ((intZeroAdd (polyEval point dividend)).symm.trans
          (congrArg (· + polyEval point dividend) (intZeroMul (polyEval point divisor)).symm))
  | fuel + 1, divisor, dividend => by
      dsimp only [polyPseudoDivMod]
      cases Nat.decLt (polyDegree dividend) (polyDegree divisor) with
      | isTrue _ =>
          show intPower (polyLeadingCoeff divisor) 0 * polyEval point dividend
            = polyEval point ([] : List Int) * polyEval point divisor + polyEval point dividend
          exact (intOneMul (polyEval point dividend)).trans
            ((intZeroAdd (polyEval point dividend)).symm.trans
              (congrArg (· + polyEval point dividend) (intZeroMul (polyEval point divisor)).symm))
      | isFalse _ =>
          have scaledDividendEval :
              polyEval point
                  (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                    (polyMul (polyMonomial (polyLeadingCoeff dividend)
                      (polyDegree dividend - polyDegree divisor)) divisor))
                = polyLeadingCoeff divisor * polyEval point dividend
                  - polyEval point (polyMonomial (polyLeadingCoeff dividend)
                      (polyDegree dividend - polyDegree divisor)) * polyEval point divisor :=
            (polyEvalSub point (polyScale (polyLeadingCoeff divisor) dividend)
                (polyMul (polyMonomial (polyLeadingCoeff dividend)
                  (polyDegree dividend - polyDegree divisor)) divisor)).trans
              ((congrArg (· - polyEval point (polyMul (polyMonomial (polyLeadingCoeff dividend)
                  (polyDegree dividend - polyDegree divisor)) divisor))
                  (polyEvalScale point (polyLeadingCoeff divisor) dividend)).trans
                (congrArg (polyLeadingCoeff divisor * polyEval point dividend - ·)
                  (polyEvalMul point (polyMonomial (polyLeadingCoeff dividend)
                    (polyDegree dividend - polyDegree divisor)) divisor)))
          have ihStep := polyPseudoDivModReconstructs point fuel divisor
            (polySub (polyScale (polyLeadingCoeff divisor) dividend)
              (polyMul (polyMonomial (polyLeadingCoeff dividend)
                (polyDegree dividend - polyDegree divisor)) divisor))
          have reducedIdentity :
              intPower (polyLeadingCoeff divisor)
                    (polyPseudoDivMod fuel divisor
                      (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                        (polyMul (polyMonomial (polyLeadingCoeff dividend)
                          (polyDegree dividend - polyDegree divisor)) divisor))).1
                  * (polyLeadingCoeff divisor * polyEval point dividend
                      - polyEval point (polyMonomial (polyLeadingCoeff dividend)
                          (polyDegree dividend - polyDegree divisor)) * polyEval point divisor)
                = polyEval point
                    (polyPseudoDivMod fuel divisor
                      (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                        (polyMul (polyMonomial (polyLeadingCoeff dividend)
                          (polyDegree dividend - polyDegree divisor)) divisor))).2.1
                  * polyEval point divisor
                  + polyEval point
                    (polyPseudoDivMod fuel divisor
                      (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                        (polyMul (polyMonomial (polyLeadingCoeff dividend)
                          (polyDegree dividend - polyDegree divisor)) divisor))).2.2 :=
            (congrArg
              (intPower (polyLeadingCoeff divisor)
                  (polyPseudoDivMod fuel divisor
                    (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                      (polyMul (polyMonomial (polyLeadingCoeff dividend)
                        (polyDegree dividend - polyDegree divisor)) divisor))).1 * ·)
              scaledDividendEval).symm.trans ihStep
          refine Eq.trans (polyPseudoDivStepArith
            (intPower (polyLeadingCoeff divisor)
              (polyPseudoDivMod fuel divisor
                (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                  (polyMul (polyMonomial (polyLeadingCoeff dividend)
                    (polyDegree dividend - polyDegree divisor)) divisor))).1)
            (polyEval point dividend)
            (polyEval point (polyMonomial (polyLeadingCoeff dividend)
              (polyDegree dividend - polyDegree divisor)))
            (polyEval point
              (polyPseudoDivMod fuel divisor
                (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                  (polyMul (polyMonomial (polyLeadingCoeff dividend)
                    (polyDegree dividend - polyDegree divisor)) divisor))).2.1)
            (polyEval point divisor)
            (polyEval point
              (polyPseudoDivMod fuel divisor
                (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                  (polyMul (polyMonomial (polyLeadingCoeff dividend)
                    (polyDegree dividend - polyDegree divisor)) divisor))).2.2)
            (polyLeadingCoeff divisor)
            reducedIdentity) ?_
          exact congrArg
            (· * polyEval point divisor
              + polyEval point
                (polyPseudoDivMod fuel divisor
                  (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                    (polyMul (polyMonomial (polyLeadingCoeff dividend)
                      (polyDegree dividend - polyDegree divisor)) divisor))).2.2)
            ((polyEvalAdd point
                (polyScale (intPower (polyLeadingCoeff divisor)
                  (polyPseudoDivMod fuel divisor
                    (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                      (polyMul (polyMonomial (polyLeadingCoeff dividend)
                        (polyDegree dividend - polyDegree divisor)) divisor))).1)
                  (polyMonomial (polyLeadingCoeff dividend)
                    (polyDegree dividend - polyDegree divisor)))
                (polyPseudoDivMod fuel divisor
                  (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                    (polyMul (polyMonomial (polyLeadingCoeff dividend)
                      (polyDegree dividend - polyDegree divisor)) divisor))).2.1).trans
              (congrArg (· + polyEval point
                  (polyPseudoDivMod fuel divisor
                    (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                      (polyMul (polyMonomial (polyLeadingCoeff dividend)
                        (polyDegree dividend - polyDegree divisor)) divisor))).2.1)
                (polyEvalScale point
                  (intPower (polyLeadingCoeff divisor)
                    (polyPseudoDivMod fuel divisor
                      (polySub (polyScale (polyLeadingCoeff divisor) dividend)
                        (polyMul (polyMonomial (polyLeadingCoeff dividend)
                          (polyDegree dividend - polyDegree divisor)) divisor))).1)
                  (polyMonomial (polyLeadingCoeff dividend)
                    (polyDegree dividend - polyDegree divisor))))).symm

/-! ## Groundings -/

/-- `x² − 1` divided by the monic `x + 1` is `x − 1` remainder `0`:
`polyDivModMonic 3 [1, 1] [-1, 0, 1] = ([-1, 1], [0, 0, 0])` (the remainder is the untrimmed zero
polynomial — trimming to `[]` is `polyTrim`'s job, not the divider's). -/
theorem polyDivModMonicDifferenceOfSquares :
    polyDivModMonic 3 [1, 1] [-1, 0, 1] = ([-1, 1], [0, 0, 0]) := by decide

/-- `x² + 1` divided by the monic `x` leaves remainder `1` (as the untrimmed `[1, 0, 0]`): the quotient
is `x`, and `polyLeadingCoeff` of the remainder is `1`. -/
theorem polyDivModMonicRemainderExample :
    (polyDivModMonic 3 [0, 1] [1, 0, 1]).2 = [1, 0, 0] := by decide

/-- The reconstruction exhibited at `x = 4` on `x²−1 = (x−1)(x+1)`: `eval(dividend) = eval(quotient)·eval(divisor)
+ eval(remainder)`, a `decide` cross-check of `polyDivModMonicReconstructs`. -/
theorem polyDivModMonicReconstructsGroundingAtFour :
    polyEval 4 [-1, 0, 1]
      = polyEval 4 (polyDivModMonic 3 [1, 1] [-1, 0, 1]).1 * polyEval 4 [1, 1]
        + polyEval 4 (polyDivModMonic 3 [1, 1] [-1, 0, 1]).2 := by decide

/-- `x + 1` divides `x² − 1` exactly: the remainder trims to the zero polynomial. -/
theorem polyLinearFactorDividesDifferenceOfSquares :
    polyTrim (polyDivModMonic 3 [1, 1] [-1, 0, 1]).2 = [] := by decide

/-- The exact-division consequence exhibited at `x = 7` (`48 = 6 · 8`): with `x + 1` dividing `x² − 1`,
`eval(x²−1) = eval(quotient) · eval(x+1)`, a `decide` cross-check of `polyDividesMonicEvalMultiple`. -/
theorem polyDividesMonicEvalMultipleGroundingAtSeven :
    polyEval 7 [-1, 0, 1] = polyEval 7 (polyDivModMonic 3 [1, 1] [-1, 0, 1]).1 * polyEval 7 [1, 1] := by
  decide

/-- The non-monic `2x + 1` pseudo-divides `2x² + 3x + 1 = (2x+1)(x+1)` exactly (remainder trims to zero) —
`polyDivModMonic` could not do this (leading coefficient `2 ≠ 1`), but pseudo-division stays integral. -/
theorem polyPseudoDivModDividesExactly :
    polyTrim (polyPseudoDivMod 3 [1, 2] [1, 3, 2]).2.2 = [] := by decide

/-- The subresultant reconstruction exhibited at `x = 5` on `2x²+3x+1` by `2x+1` (leading coefficient `2`):
`2^scalePower · eval(dividend) = eval(quotient)·eval(divisor) + eval(remainder)`, a `decide` cross-check of
`polyPseudoDivModReconstructs`. -/
theorem polyPseudoDivModReconstructsGroundingAtFive :
    intPower (polyLeadingCoeff [1, 2]) (polyPseudoDivMod 3 [1, 2] [1, 3, 2]).1 * polyEval 5 [1, 3, 2]
      = polyEval 5 (polyPseudoDivMod 3 [1, 2] [1, 3, 2]).2.1 * polyEval 5 [1, 2]
        + polyEval 5 (polyPseudoDivMod 3 [1, 2] [1, 3, 2]).2.2 := by decide

/-- Marker: the ℤ[x] division layer ships with monic division (`dividend = quotient · divisor + remainder`)
and its exact-division corollary, AND ℤ-native pseudo-division for an ARBITRARY divisor
(`leadDivisor^scalePower · dividend = quotient · divisor + remainder`, `polyPseudoDivModReconstructs`) —
the subresultant identity the Euclidean GCD runs on, with no rationals.  Both reconstructions are proved at
the evaluation level fuel-independently.  The degree bound `deg remainder < deg divisor` (the GCD's
termination lever) is the next brick. -/
def fxIntPoly_hasMonicDivisionReconstruction : Bool := true

end FX1Poly.ComputerAlgebra
