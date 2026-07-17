import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore
import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Number.IntAddAssociativity
import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntUnivariatePolynomial — the ℤ[x] substrate
(the first brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

`EndomorphismMinimalPolynomial` closed the TOP invariant factor (the minimal polynomial) as a proven
∀-refutation, and named the honest remaining gap: the FULL invariant-factor LIST needs univariate
polynomial GCD (Euclidean over ℚ[x] / pseudo-division over ℤ[x]), NOT eigenvalue factoring.  This file
opens that arc with the polynomial ring itself.

## The representation

A univariate integer polynomial is its ASCENDING coefficient list: `[c₀, c₁, …, cₙ]` denotes
`c₀ + c₁·x + ⋯ + cₙ·xⁿ`.  Trailing zeros are permitted (no normalization is forced), so the type is plain
`List Int` and every operation is structural — the exact `decide`-friendly, propext-free discipline the lane
uses.  This is the SAME coefficient convention as `matrixPolyEval`, so the two evaluation engines agree.

## What is PROVEN (the ring homomorphism under evaluation)

Evaluation `polyEval x` is a ring homomorphism `ℤ[x] → ℤ`: it commutes with `+`, with scalar `·`, and with
`×`, machine-proved by structural induction — `polyEvalAdd`, `polyEvalScale`, `polyEvalMul`.  The
multiplication case is the discrete-convolution correctness of `polyMul`, the substantive lemma the later
GCD/Bézout steps rest on (a correct product is what makes the Euclidean remainder meaningful).

## Zero-axiom design

All arithmetic routes through the corpus `Int` lemmas (`intLeftDistrib`, `intRightDistrib`, `intMulAssoc`,
`intAddAssoc`, `intAddComm`, `intMulComm`, `intZeroMul`, `intMulZero`, …).  Every definition is structural on
the coefficient list; groundings close by `decide`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntUnivariatePolynomial.lean`.
-/

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

/-- Marker: the ℤ[x] substrate ships with evaluation proved to be a ring homomorphism (additive,
homogeneous, multiplicative), the foundation for the invariant-factor GCD.  The Euclidean division / GCD
layer (and its Bézout certificates) is the next brick. -/
def fxIntPoly_hasEvaluationRingHomomorphism : Bool := true

end FX1Poly.ComputerAlgebra
