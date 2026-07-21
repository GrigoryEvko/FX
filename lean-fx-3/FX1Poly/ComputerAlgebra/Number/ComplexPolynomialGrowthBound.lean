import FX1Poly.ComputerAlgebra.Number.ComplexPolynomial
import FX1Poly.ComputerAlgebra.Number.RealOrderMonotoneMultiply

/-! # ComplexPolynomialGrowthBound — the complex polynomial growth bound

Horner evaluation of a complex polynomial is dominated in modulus by the Horner
sum of the coefficient moduli,

  `|p(z)| ≤ |c₀| + |z|·(|c₁| + |z|·(|c₂| + ⋯))`,

the `Σ|cᵢ|·|z|ⁱ` bound in Horner shape — a step toward the constructive
Fundamental Theorem of Algebra.  The ingredients are the modulus triangle
inequality (`modulusTriangleInequality`), modulus multiplicativity
(`modulusMulDenotesSame`), and order-monotone multiplication by a nonnegative
real (`realMulLeftMonotone`).

`hornerModulusBound point` is the coefficientwise structural analogue of
`evalComplexPoly point` with `modulus` on each coefficient and `modulus point` as
the Horner multiplier.  `modulusEvalLeHornerBound` proves the bound by list
induction:

* `[]`: `|p(z)| = |0| ~ 0`, and `~` tightens to `≤`.  `|0| ~ 0` is
  `squareZeroImpliesZero` on the squared-modulus collapse `|0|² ~ 0`.
* `coeff :: rest`: the Horner head `|c + z·p'(z)|` clears the triangle inequality
  to `|c| + |z·p'(z)|`, multiplicativity denotes `|z·p'(z)| ~ |z|·|p'(z)|`, and
  the inductive hypothesis `|p'(z)| ≤ bound'` lifts through `realMulLeftMonotone`
  (`|z| ≥ 0`) and `lessEqualRealAddCompatLeft` (shared `|c|`) to `|c| + |z|·bound'`.

The left factor `modulus point` needs pointwise nonnegativity, from
`modulusIsNonNegativeReal`.  Structural recursion on the coefficient list; the
arithmetic routes only through setoid congruences and the order corpus, and no
real `≤`/equality is ever case-split.  Zero axioms. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-- The modulus is a pointwise-nonnegative real: `|z| = sqrtReal |z|²` and every
`sqrtReal` approximant is a nonnegative rational square root. -/
theorem modulusIsNonNegativeReal (value : ComplexReal) : IsNonNegativeReal (modulus value) :=
  sqrtRealIsNonNegativeReal (modulusSquared value) (modulusSquaredIsNonNegativeReal value)

/-- `|0| ~ 0`: the squared modulus of the complex zero collapses (`0·0 + 0·0 ~ 0`),
so `|0|² ~ 0`, and square-zero cancellation sends `|0|` itself to `0`. -/
theorem modulusZeroComplexDenotesZero :
    DenotesSameReal (modulus zeroComplex) (constantReal zeroRational) :=
  have squaredCollapses :
      DenotesSameReal (modulusSquared zeroComplex) (constantReal zeroRational) :=
    denotesSameRealTrans
      (addRealRespectsDenotesSame
        (mulRealZeroRight (constantReal zeroRational))
        (mulRealZeroRight (constantReal zeroRational)))
      (addRealZeroRight (constantReal zeroRational))
  squareZeroImpliesZero
    (denotesSameRealTrans
      (modulusSquareDenotesModulusSquared zeroComplex) squaredCollapses)

/-- The Horner sum of coefficient moduli: `|c₀| + |point|·(|c₁| + |point|·(⋯))`, the structural
coefficientwise analogue of `evalComplexPoly point` under `modulus`, dominating `|p(point)|`. -/
def hornerModulusBound (point : ComplexReal) : List ComplexReal → RegularReal
  | [] => constantReal zeroRational
  | coeff :: restCoeffs =>
      addReal (modulus coeff) (mulReal (modulus point) (hornerModulusBound point restCoeffs))

/-- The polynomial growth bound `|p(point)| ≤ Σ|cᵢ|·|point|ⁱ` in Horner shape: the
modulus of a Horner-evaluated complex polynomial is dominated by the Horner sum of
its coefficient moduli.  Induction on the coefficient list — the empty polynomial
evaluates to `0` with `|0| ~ 0` as the bound; the Horner head
`|coeff + point·p'(point)|` clears the triangle inequality, denotes
`|coeff| + |point|·|p'(point)|` by multiplicativity, and the inductive bound lifts
through nonnegative-scale monotonicity and shared-summand compatibility. -/
theorem modulusEvalLeHornerBound (point : ComplexReal) :
    ∀ poly : List ComplexReal,
      LessEqualReal (modulus (evalComplexPoly point poly)) (hornerModulusBound point poly)
  | [] =>
      lessEqualRealCongr (denotesSameRealRefl (modulus zeroComplex))
        modulusZeroComplexDenotesZero (lessEqualRealRefl (modulus zeroComplex))
  | coeff :: restCoeffs =>
      let tailEvaluation := evalComplexPoly point restCoeffs
      let headTerm := mulComplex point tailEvaluation
      have stepTriangle :
          LessEqualReal (modulus (addComplex coeff headTerm))
            (addReal (modulus coeff) (modulus headTerm)) :=
        modulusTriangleInequality coeff headTerm
      have headModulusDenotesProduct :
          DenotesSameReal (addReal (modulus coeff) (modulus headTerm))
            (addReal (modulus coeff) (mulReal (modulus point) (modulus tailEvaluation))) :=
        addRealRespectsDenotesSame (denotesSameRealRefl (modulus coeff))
          (modulusMulDenotesSame point tailEvaluation)
      have stepAboveProduct :
          LessEqualReal (modulus (addComplex coeff headTerm))
            (addReal (modulus coeff) (mulReal (modulus point) (modulus tailEvaluation))) :=
        lessEqualRealCongr (denotesSameRealRefl (modulus (addComplex coeff headTerm)))
          headModulusDenotesProduct stepTriangle
      have stepMonotone :
          LessEqualReal
            (addReal (modulus coeff) (mulReal (modulus point) (modulus tailEvaluation)))
            (addReal (modulus coeff)
              (mulReal (modulus point) (hornerModulusBound point restCoeffs))) :=
        lessEqualRealAddCompatLeft (modulus coeff)
          (realMulLeftMonotone (modulusIsNonNegativeReal point)
            (modulusEvalLeHornerBound point restCoeffs))
      lessEqualRealTrans stepAboveProduct stepMonotone

/-- Marker: the complex modulus satisfies the polynomial growth bound
`|p(z)| ≤ Σ|cᵢ||z|ⁱ` (Horner form) on the Gaussian-real setoid. -/
def fxComplexReal_hasPolynomialGrowthBound : Bool := true

end FX1Poly.ComputerAlgebra
