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

The degree bound `deg remainder < deg divisor` (needed for uniqueness and for the Euclidean GCD's
termination) is the honest remaining step, tracked as the next brick.

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

/-- Marker: the ℤ[x] monic division-with-remainder algorithm ships with the reconstruction identity
`dividend = quotient · divisor + remainder` proved at the evaluation level, fuel-independently.  The
degree bound `deg remainder < deg divisor` (the Euclidean-GCD termination lever) is the next brick. -/
def fxIntPoly_hasMonicDivisionReconstruction : Bool := true

end FX1Poly.ComputerAlgebra
