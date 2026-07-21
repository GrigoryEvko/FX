import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore
import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Number.IntAddAssociativity
import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity
import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntPower

/-! # IntUnivariatePolynomial — the ℤ[x] substrate

A univariate integer polynomial is its ascending coefficient list: `[c₀, c₁, …, cₙ]` denotes
`c₀ + c₁·x + ⋯ + cₙ·xⁿ`.  Trailing zeros are permitted (no normalization is forced), so the type is plain
`List Int` and every operation is structural.  This is the same coefficient convention as `matrixPolyEval`,
so the two evaluation engines agree.

Evaluation `polyEval x` is a ring homomorphism `ℤ[x] → ℤ`: it commutes with `+`, scalar `·`, and `×`
(`polyEvalAdd`, `polyEvalScale`, `polyEvalMul`, the last being the discrete-convolution correctness of
`polyMul`), with negation and subtraction, composition as substitution, powers, the semantic ring laws, and
monomials.  Also here: the linear factor `x − root` and the factor-theorem bridge (factor ⟹ root).  This is
the foundation for the invariant-factor GCD.

All arithmetic routes through the corpus `Int` lemmas; every definition is structural on the coefficient
list.  Free of `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The polynomial operations (structural on the ascending coefficient list) -/

/-- Entrywise coefficient sum with tail padding: `(c₀+d₀) + (c₁+d₁)·x + ⋯`, the longer polynomial's tail
carried through unchanged. -/
def polyAdd : List Int → List Int → List Int
  | [], rightPoly => rightPoly
  | leftPoly, [] => leftPoly
  | leftHead :: leftTail, rightHead :: rightTail =>
      (leftHead + rightHead) :: polyAdd leftTail rightTail

/-- Scalar multiple: `scalar·c₀ + scalar·c₁·x + ⋯`. -/
def polyScale (scalar : Int) : List Int → List Int
  | [] => []
  | coeff :: restCoeffs => (scalar * coeff) :: polyScale scalar restCoeffs

/-- Polynomial product by convolution: `(c₀ + x·p')·q = c₀·q + x·(p'·q)`, the shift `x·(·)` realized by a
leading `0`. -/
def polyMul : List Int → List Int → List Int
  | [], _ => []
  | leftHead :: leftTail, rightPoly =>
      polyAdd (polyScale leftHead rightPoly) (0 :: polyMul leftTail rightPoly)

/-- Horner evaluation of the ascending coefficient list at `x`: `c₀ + x·(c₁ + x·(c₂ + ⋯))`. -/
def polyEval (point : Int) : List Int → Int
  | [] => 0
  | coeff :: restCoeffs => coeff + point * polyEval point restCoeffs

/-! ## The middle-four interchange (the add-rearrangement the homomorphism proofs need) -/

/-- `(a + b) + (c + d) = (a + c) + (b + d)` over ℤ — associativity and commutativity of addition. -/
theorem intAddInterchange (valueA valueB valueC valueD : Int) :
    (valueA + valueB) + (valueC + valueD) = (valueA + valueC) + (valueB + valueD) :=
  (intAddAssoc valueA valueB (valueC + valueD)).trans
    ((congrArg (valueA + ·) (intAddAssoc valueB valueC valueD).symm).trans
      ((congrArg (fun middle => valueA + (middle + valueD)) (intAddComm valueB valueC)).trans
        ((congrArg (valueA + ·) (intAddAssoc valueC valueB valueD)).trans
          (intAddAssoc valueA valueC (valueB + valueD)).symm)))

/-! ## Evaluation is a ring homomorphism (PROVEN by structural induction) -/

/-- **Additivity.**  `eval(p + q) = eval(p) + eval(q)`. -/
theorem polyEvalAdd (point : Int) :
    ∀ leftPoly rightPoly : List Int,
      polyEval point (polyAdd leftPoly rightPoly)
        = polyEval point leftPoly + polyEval point rightPoly
  | [], rightPoly => (intZeroAdd (polyEval point rightPoly)).symm
  | _ :: _, [] => (intAddZero _).symm
  | leftHead :: leftTail, rightHead :: rightTail =>
      (congrArg (fun tailValue => (leftHead + rightHead) + point * tailValue)
          (polyEvalAdd point leftTail rightTail)).trans
        ((congrArg ((leftHead + rightHead) + ·)
            (intLeftDistrib point (polyEval point leftTail) (polyEval point rightTail))).trans
          (intAddInterchange leftHead rightHead
            (point * polyEval point leftTail) (point * polyEval point rightTail)))

/-- **Scalar homogeneity.**  `eval(scalar · p) = scalar · eval(p)`. -/
theorem polyEvalScale (point scalar : Int) :
    ∀ coeffs : List Int, polyEval point (polyScale scalar coeffs) = scalar * polyEval point coeffs
  | [] => (intMulZero scalar).symm
  | coeff :: restCoeffs =>
      (congrArg (fun tailValue => scalar * coeff + point * tailValue)
          (polyEvalScale point scalar restCoeffs)).trans
        ((congrArg (scalar * coeff + ·)
            ((intMulAssoc point scalar (polyEval point restCoeffs)).symm.trans
              ((congrArg (· * polyEval point restCoeffs) (intMulComm point scalar)).trans
                (intMulAssoc scalar point (polyEval point restCoeffs))))).trans
          (intLeftDistrib scalar coeff (point * polyEval point restCoeffs)).symm)

/-- **Multiplicativity.**  `eval(p × q) = eval(p) × eval(q)` — the discrete-convolution correctness of
`polyMul`, by induction on the left polynomial. -/
theorem polyEvalMul (point : Int) :
    ∀ leftPoly rightPoly : List Int,
      polyEval point (polyMul leftPoly rightPoly)
        = polyEval point leftPoly * polyEval point rightPoly
  | [], rightPoly => (intZeroMul (polyEval point rightPoly)).symm
  | leftHead :: leftTail, rightPoly =>
      (polyEvalAdd point (polyScale leftHead rightPoly) (0 :: polyMul leftTail rightPoly)).trans
        ((congrArg (· + polyEval point (0 :: polyMul leftTail rightPoly))
            (polyEvalScale point leftHead rightPoly)).trans
          ((congrArg (leftHead * polyEval point rightPoly + ·)
              ((congrArg (fun tailValue => (0 : Int) + point * tailValue)
                  (polyEvalMul point leftTail rightPoly)).trans
                (intZeroAdd (point * (polyEval point leftTail * polyEval point rightPoly))))).trans
            ((intRightDistrib leftHead (point * polyEval point leftTail) (polyEval point rightPoly)).trans
              (congrArg (leftHead * polyEval point rightPoly + ·)
                (intMulAssoc point (polyEval point leftTail) (polyEval point rightPoly)))).symm))

/-! ## Negation and subtraction (the remainder `f − q·g` needs a difference) -/

/-- Coefficientwise negation: `-c₀ + -c₁·x + ⋯`. -/
def polyNeg : List Int → List Int
  | [] => []
  | coeff :: restCoeffs => -coeff :: polyNeg restCoeffs

/-- Polynomial difference: `leftPoly + (-rightPoly)`, the shape a Euclidean/pseudo-division remainder
takes. -/
def polySub (leftPoly rightPoly : List Int) : List Int :=
  polyAdd leftPoly (polyNeg rightPoly)

/-- **Evaluation negates.**  `eval(-p) = -eval(p)`, by structural induction — `intMulNeg` pushes the
negation past the Horner multiplier, `intNegAdd` past the sum. -/
theorem polyEvalNeg (point : Int) :
    ∀ coeffs : List Int, polyEval point (polyNeg coeffs) = -(polyEval point coeffs)
  | [] => intNegZero.symm
  | coeff :: restCoeffs =>
      (congrArg (fun tailValue => -coeff + point * tailValue) (polyEvalNeg point restCoeffs)).trans
        ((congrArg (-coeff + ·) (intMulNeg point (polyEval point restCoeffs))).trans
          (intNegAdd coeff (point * polyEval point restCoeffs)).symm)

/-- **Evaluation is subtractive.**  `eval(p − q) = eval(p) − eval(q)` — additivity composed with
negation. -/
theorem polyEvalSub (point : Int) (leftPoly rightPoly : List Int) :
    polyEval point (polySub leftPoly rightPoly)
      = polyEval point leftPoly - polyEval point rightPoly :=
  (polyEvalAdd point leftPoly (polyNeg rightPoly)).trans
    ((congrArg (polyEval point leftPoly + ·) (polyEvalNeg point rightPoly)).trans
      (intSubEqAddNeg (polyEval point leftPoly) (polyEval point rightPoly)).symm)

/-! ## The linear factor and the root theorem (factor ⟹ root)

The polynomial-ring bridge for eigenvalues: any multiple of `x − root` vanishes at `root`
(`polyEval root ((x − root) · cofactor) = 0`), riding `polyEvalMul` with no degree machinery. -/

/-- The linear factor `x − root`, i.e. the ascending list `[-root, 1]`. -/
def polyLinearFactor (root : Int) : List Int := [-root, 1]

/-- The constant polynomial `1` evaluates to `1` at every point. -/
theorem polyEvalOne (point : Int) : polyEval point [1] = 1 :=
  (congrArg (1 + ·) (intMulZero point)).trans (intAddZero 1)

/-- **Linear factor evaluates to the shift.**  `eval_point(x − root) = point − root`. -/
theorem polyEvalLinearFactor (point root : Int) :
    polyEval point (polyLinearFactor root) = point - root :=
  (congrArg (fun tailValue => -root + point * tailValue) (polyEvalOne point)).trans
    ((congrArg (-root + ·) (intMulOne point)).trans
      ((intAddComm (-root) point).trans (intSubEqAddNeg point root).symm))

/-- **The linear factor vanishes at its root.**  `eval_root(x − root) = 0`. -/
theorem polyLinearFactorVanishesAtRoot (root : Int) :
    polyEval root (polyLinearFactor root) = 0 :=
  (polyEvalLinearFactor root root).trans
    ((intSubEqAddNeg root root).trans (intAddRightNeg root))

/-- **Root theorem, factor ⟹ root.**  Any multiple of `x − root` vanishes at `root` — the constructive
direction of "`x − root` divides `p` iff `root` is a root of `p`". -/
theorem polyLinearFactorRootAnnihilatesMultiple (root : Int) (cofactor : List Int) :
    polyEval root (polyMul (polyLinearFactor root) cofactor) = 0 :=
  (polyEvalMul root (polyLinearFactor root) cofactor).trans
    ((congrArg (· * polyEval root cofactor) (polyLinearFactorVanishesAtRoot root)).trans
      (intZeroMul (polyEval root cofactor)))

/-! ## Composition (the substitution homomorphism) -/

/-- The constant polynomial `[c]` evaluates to `c` at every point (`polyEvalOne`'s generalization). -/
theorem polyEvalConstant (point constant : Int) : polyEval point [constant] = constant :=
  (congrArg (constant + ·) (intMulZero point)).trans (intAddZero constant)

/-- Polynomial composition `outer ∘ inner`: substitute `inner` for the variable of `outer`.  By Horner,
`(c₀ + x·outer') ∘ inner = c₀ + inner · (outer' ∘ inner)`. -/
def polyCompose : List Int → List Int → List Int
  | [], _ => []
  | outerHead :: outerTail, inner =>
      polyAdd [outerHead] (polyMul inner (polyCompose outerTail inner))

/-- **Composition is substitution under evaluation.**  `eval_point(outer ∘ inner) = eval_{eval_point(inner)}(outer)`
— the substitution ring homomorphism, by induction on `outer` riding `polyEvalAdd`/`polyEvalMul`. -/
theorem polyEvalCompose (point : Int) :
    ∀ outer inner : List Int,
      polyEval point (polyCompose outer inner) = polyEval (polyEval point inner) outer
  | [], _ => rfl
  | outerHead :: outerTail, inner =>
      (polyEvalAdd point [outerHead] (polyMul inner (polyCompose outerTail inner))).trans
        ((congrArg (· + polyEval point (polyMul inner (polyCompose outerTail inner)))
            (polyEvalConstant point outerHead)).trans
          (congrArg (outerHead + ·)
            ((polyEvalMul point inner (polyCompose outerTail inner)).trans
              (congrArg (polyEval point inner * ·) (polyEvalCompose point outerTail inner)))))

/-! ## Powers and the semantic ring laws

Polynomial powers are the `xᵏ ↦ Mᵏ` shape `matrixPolyEval` consumes.  Multiplication is commutative and
associative under evaluation even though the coefficient-list representation is non-canonical (trailing
zeros), because ℤ is. -/

/-- Polynomial power `base^exponent` (the constant `1` at exponent `0`, one more factor per successor). -/
def polyPow (base : List Int) : Nat → List Int
  | 0 => [1]
  | exponentValue + 1 => polyMul (polyPow base exponentValue) base

/-- **Evaluation is power-multiplicative.**  `eval_point(base^n) = eval_point(base)^n`, by induction on the
exponent riding `polyEvalMul`; matches the corpus `intPower` (both base/successor cases definitional). -/
theorem polyEvalPow (point : Int) (base : List Int) :
    ∀ exponentValue : Nat,
      polyEval point (polyPow base exponentValue) = intPower (polyEval point base) exponentValue
  | 0 => polyEvalOne point
  | exponentValue + 1 =>
      (polyEvalMul point (polyPow base exponentValue) base).trans
        (congrArg (· * polyEval point base) (polyEvalPow point base exponentValue))

/-- **Multiplication commutes under evaluation.**  `eval_point(p · q) = eval_point(q · p)` — ℤ's
commutativity lifted through `polyEvalMul`, holding despite the non-canonical list representation. -/
theorem polyEvalMulComm (point : Int) (leftPoly rightPoly : List Int) :
    polyEval point (polyMul leftPoly rightPoly) = polyEval point (polyMul rightPoly leftPoly) :=
  (polyEvalMul point leftPoly rightPoly).trans
    ((intMulComm (polyEval point leftPoly) (polyEval point rightPoly)).trans
      (polyEvalMul point rightPoly leftPoly).symm)

/-- **Multiplication associates under evaluation.**  `eval_point((p · q) · r) = eval_point(p · (q · r))`. -/
theorem polyEvalMulAssoc (point : Int) (leftPoly midPoly rightPoly : List Int) :
    polyEval point (polyMul (polyMul leftPoly midPoly) rightPoly)
      = polyEval point (polyMul leftPoly (polyMul midPoly rightPoly)) :=
  (polyEvalMul point (polyMul leftPoly midPoly) rightPoly).trans
    ((congrArg (· * polyEval point rightPoly) (polyEvalMul point leftPoly midPoly)).trans
      ((intMulAssoc (polyEval point leftPoly) (polyEval point midPoly) (polyEval point rightPoly)).trans
        (((congrArg (polyEval point leftPoly * ·) (polyEvalMul point midPoly rightPoly)).symm).trans
          (polyEvalMul point leftPoly (polyMul midPoly rightPoly)).symm)))

/-! ## Monomials (`coeff · xⁿ`, the shape a division quotient's terms take) -/

/-- The monomial `coeff · x^degree`: `degree` leading zeros followed by the coefficient. -/
def polyMonomial (coeff : Int) : Nat → List Int
  | 0 => [coeff]
  | degree + 1 => 0 :: polyMonomial coeff degree

/-- **Monomial evaluation.**  `eval_point(coeff · x^degree) = coeff · point^degree`, by induction on the
degree — each leading zero contributes a `point·(…)` Horner factor, matching `intPower`. -/
theorem polyEvalMonomial (point coeff : Int) :
    ∀ degree : Nat, polyEval point (polyMonomial coeff degree) = coeff * intPower point degree
  | 0 => (polyEvalConstant point coeff).trans (intMulOne coeff).symm
  | degree + 1 =>
      (intZeroAdd (point * polyEval point (polyMonomial coeff degree))).trans
        ((congrArg (point * ·) (polyEvalMonomial point coeff degree)).trans
          ((intMulComm point (coeff * intPower point degree)).trans
            (intMulAssoc coeff (intPower point degree) point)))

/-! ## Groundings -/

/-- `(x − 1)(x + 1) = x² − 1`: `polyMul [-1, 1] [1, 1] = [-1, 0, 1]`. -/
theorem polyMulDifferenceOfSquaresExample :
    polyMul [-1, 1] [1, 1] = [-1, 0, 1] := by decide

/-- Evaluation of `x² − 1` at `3` is `8` (`= 3² − 1`). -/
theorem polyEvalDifferenceOfSquaresAtThree :
    polyEval 3 [-1, 0, 1] = 8 := by decide

/-- The multiplicativity homomorphism, exhibited concretely: `eval((x−1)(x+1)) = eval(x−1)·eval(x+1)` at
`x = 5` (`24 = 4 · 6`), a `decide` cross-check of `polyEvalMul`. -/
theorem polyEvalMulGroundingAtFive :
    polyEval 5 (polyMul [-1, 1] [1, 1]) = polyEval 5 [-1, 1] * polyEval 5 [1, 1] := by decide

/-- `(3 + 2x) − (1 + 2x) = 2`: `polySub [3, 2] [1, 2] = [2, 0]` (the `x` coefficients cancel). -/
theorem polySubCancelsLinearTermExample :
    polySub [3, 2] [1, 2] = [2, 0] := by decide

/-- The subtractive homomorphism exhibited: `eval((3+2x) − (1+2x)) = eval(3+2x) − eval(1+2x)` at `x = 5`
(`2 = 13 − 11`), a `decide` cross-check of `polyEvalSub`. -/
theorem polyEvalSubGroundingAtFive :
    polyEval 5 (polySub [3, 2] [1, 2]) = polyEval 5 [3, 2] - polyEval 5 [1, 2] := by decide

/-- `(x − 2)(x − 5) = x² − 7x + 10`: `polyMul (polyLinearFactor 2) (polyLinearFactor 5) = [10, -7, 1]`. -/
theorem polyLinearFactorProductExample :
    polyMul (polyLinearFactor 2) (polyLinearFactor 5) = [10, -7, 1] := by decide

/-- `2` is a root of `(x − 2)(x − 5)`: `polyEval 2 [10, -7, 1] = 0` (`= 4 − 14 + 10`). -/
theorem polyLinearFactorProductVanishesAtTwo :
    polyEval 2 (polyMul (polyLinearFactor 2) (polyLinearFactor 5)) = 0 := by decide

/-- `5` is likewise a root of `(x − 2)(x − 5)`: `polyEval 5 [10, -7, 1] = 0` (`= 25 − 35 + 10`), the second
factor's root — the factor-theorem bridge exhibited on a concrete degree-2 product. -/
theorem polyLinearFactorProductVanishesAtFive :
    polyEval 5 (polyMul (polyLinearFactor 2) (polyLinearFactor 5)) = 0 := by decide

/-- Composing the constant `5` with any polynomial evaluates to `5` everywhere (trailing-zero-robust
form of "a constant composes to itself"): `polyEval 9 (polyCompose [5] [7, 2]) = 5`. -/
theorem polyComposeConstantExample : polyEval 9 (polyCompose [5] [7, 2]) = 5 := by decide

/-- The substitution homomorphism exhibited: `(x² + 1) ∘ (x + 3)` evaluated at `2` equals `x² + 1`
evaluated at `(2 + 3) = 5`, i.e. `26 = 26`, a `decide` cross-check of `polyEvalCompose`. -/
theorem polyEvalComposeGroundingAtTwo :
    polyEval 2 (polyCompose [1, 0, 1] [3, 1]) = polyEval (polyEval 2 [3, 1]) [1, 0, 1] := by decide

/-- The power homomorphism exhibited: `x³` at `2` is `2³ = 8`: `polyEval 2 (polyPow [0, 1] 3) = intPower (polyEval 2 [0, 1]) 3`. -/
theorem polyEvalPowGroundingCube :
    polyEval 2 (polyPow [0, 1] 3) = intPower (polyEval 2 [0, 1]) 3 := by decide

/-- `(x + 1)²` at `2` is `3² = 9`, a second `decide` cross-check of `polyEvalPow`. -/
theorem polyEvalPowGroundingBinomial :
    polyEval 2 (polyPow [1, 1] 2) = intPower (polyEval 2 [1, 1]) 2 := by decide

/-- `3x²` is `[0, 0, 3]`: `polyMonomial 3 2 = [0, 0, 3]`. -/
theorem polyMonomialExample : polyMonomial 3 2 = [0, 0, 3] := by decide

/-- `3x²` at `2` is `3 · 4 = 12`: `polyEval 2 (polyMonomial 3 2) = 3 * intPower 2 2`, a `decide` cross-check
of `polyEvalMonomial`. -/
theorem polyEvalMonomialGrounding :
    polyEval 2 (polyMonomial 3 2) = 3 * intPower 2 2 := by decide

end FX1Poly.ComputerAlgebra
