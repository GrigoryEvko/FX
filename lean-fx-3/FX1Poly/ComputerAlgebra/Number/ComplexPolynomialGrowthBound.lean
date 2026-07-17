import FX1Poly.ComputerAlgebra.Number.ComplexPolynomial
import FX1Poly.ComputerAlgebra.Number.RealOrderMonotoneMultiply

/-! # ComplexPolynomialGrowthBound — the ℂ polynomial growth bound (FTA path)

The capstone of the ℂ-analysis foundation toward the constructive fundamental theorem of algebra:
Horner evaluation of a complex polynomial is dominated in modulus by the Horner sum of the
coefficient moduli,

  `|p(z)| ≤ |c₀| + |z|·(|c₁| + |z|·(|c₂| + ⋯))`,

the exact `Σ|cᵢ|·|z|ⁱ` bound in Horner shape.  Every ingredient shipped: the ℂ modulus triangle
inequality (`modulusTriangleInequality`), modulus multiplicativity (`modulusMulDenotesSame`), and —
the last missing piece — order-monotone multiplication by a nonnegative real (`realMulLeftMonotone`).

## The proof

`hornerModulusBound point` is the coefficientwise structural analogue of `evalComplexPoly point`, with
`modulus` on each coefficient and `modulus point` as the Horner multiplier.  The headline is a clean
list induction with no residual:

* `[]`: `|p(z)| = |0| ~ 0 = bound`, and `~` tightens to `≤` (`lessEqualRealRefl` transported by
  `lessEqualRealCongr`).  `|0| ~ 0` is `squareZeroImpliesZero` fed the squared-modulus collapse
  `|0|² ~ |0|² of 0 ~ 0`.
* `coeff :: rest`: the Horner head `|c + z·p'(z)|` clears the triangle inequality to
  `|c| + |z·p'(z)|`, modulus multiplicativity denotes `|z·p'(z)| ~ |z|·|p'(z)|`, and the inductive
  hypothesis `|p'(z)| ≤ bound'` lifts through `realMulLeftMonotone` (`|z| ≥ 0`) and
  `lessEqualRealAddCompatLeft` (shared `|c|`) to `|c| + |z|·bound'`, the bound at `coeff :: rest`.
  `lessEqualRealTrans` chains the two, with `lessEqualRealCongr` absorbing the multiplicativity `~`.

The left factor `modulus point` needs pointwise nonnegativity, supplied here by
`modulusIsNonNegativeReal` (the modulus is a `sqrtReal`, whose output is pointwise nonnegative).

## Zero-axiom design

Structural recursion on the coefficient list; the arithmetic routes only through the shipped setoid
congruences (`lessEqualRealCongr`, `addRealRespectsDenotesSame`, `denotesSameRealRefl/Trans`) and the
shipped order corpus (`modulusTriangleInequality`, `realMulLeftMonotone`, `lessEqualRealTrans`,
`lessEqualRealAddCompatLeft`, `lessEqualRealRefl`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`, `decide`, or `WellFounded.fix`; no real `≤`/equality is ever
case-split.  Per-declaration gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## The modulus is pointwise nonnegative -/

/-- **The modulus is a pointwise-nonnegative real** — `|z| = sqrtReal |z|²` and every `sqrtReal`
approximant is a nonnegative rational square root.  The nonnegativity the Horner multiplier
`realMulLeftMonotone` consumes. -/
theorem modulusIsNonNegativeReal (value : ComplexReal) : IsNonNegativeReal (modulus value) :=
  sqrtRealIsNonNegativeReal (modulusSquared value) (modulusSquaredIsNonNegativeReal value)

/-! ## The zero modulus collapses -/

/-- **`|0| ~ 0`** — the squared modulus of the complex zero collapses (`0·0 + 0·0 ~ 0`), so
`|0|² ~ 0`, and square-zero cancellation sends `|0|` itself to `0`.  Closes the empty-polynomial base
case. -/
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

/-! ## The Horner modulus bound -/

/-- The Horner sum of coefficient moduli: `|c₀| + |point|·(|c₁| + |point|·(⋯))`, the structural
coefficientwise analogue of `evalComplexPoly point` under `modulus`, dominating `|p(point)|`. -/
def hornerModulusBound (point : ComplexReal) : List ComplexReal → RegularReal
  | [] => constantReal zeroRational
  | coeff :: restCoeffs =>
      addReal (modulus coeff) (mulReal (modulus point) (hornerModulusBound point restCoeffs))

/-! ## The headline: the polynomial growth bound -/

/-- **The polynomial growth bound** `|p(point)| ≤ Σ|cᵢ|·|point|ⁱ` in Horner shape — the modulus of a
Horner-evaluated complex polynomial is dominated by the Horner sum of its coefficient moduli.  Induction
on the coefficient list: the empty polynomial evaluates to `0` and `|0| ~ 0` is the bound; the Horner
head `|coeff + point·p'(point)|` clears the triangle inequality, is denoted `|coeff| + |point|·|p'(point)|`
by modulus multiplicativity, and the inductive bound `|p'(point)| ≤ bound'` lifts through nonnegative-scale
monotonicity and the shared-summand compatibility to the bound at `coeff :: rest`.  The capstone of the
ℂ-analysis foundation for the constructive fundamental theorem of algebra. -/
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

/-- Marker: the ℂ modulus satisfies the polynomial growth bound `|p(z)| ≤ Σ|cᵢ||z|ⁱ` (Horner form) on
the Gaussian-real setoid — the capstone of the ℂ-analysis FTA foundation. -/
def fxComplexReal_hasPolynomialGrowthBound : Bool := true

end FX1Poly.ComputerAlgebra
