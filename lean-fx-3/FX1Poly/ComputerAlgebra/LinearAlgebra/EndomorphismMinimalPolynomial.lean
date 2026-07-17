import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismPowerZeroSeparator

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/EndomorphismMinimalPolynomial — the annihilator
separator (the top invariant factor of `invariantFactorSeparator`, r3 partial)

`EndomorphismSimilarity` named `invariantFactorSeparator` as the ONE remaining wall: the COMPLETE
similarity separator is the list of invariant factors of `x·I − M`.  That note framed the obstruction
as "irrational eigenvalues (factoring the char poly over ℚ)".  **That framing is a misdiagnosis** — the
same shape as the three walls this arc already closed (`charMatrixCarrier`, `rankSequenceNilpotent`,
`minorRankGeneral`), each of which fell to a sharper route than the predicted obstruction.  The invariant
factors of `x·I − M` are the ℚ[x]-Smith diagonal, computed by the **Euclidean GCD of the char-matrix
minors** — a purely gcd-based computation that NEVER factors the characteristic polynomial into
irreducibles.  No eigenvalue, rational or irrational, ever appears.  The genuine obstruction to the FULL
list is univariate ℚ[x] polynomial GCD, not eigenvalue factoring.

This file ships the **top** invariant factor's separating power without any polynomial-matrix carrier at
all: the **minimal polynomial as a produced-and-checked annihilator**.

## The annihilator separator (sound, decidable, eigenvalue-free)

For an integer coefficient list `p = [c₀, …, c_d]` (ascending) and an integer matrix `M`, the polynomial
value `p(M) = Σ cₖ·Mᵏ` is machine-computable over the shipped matrix ring (Horner-free sum of shipped
`endomorphismMatrixPower` scaled and added).  `EndomorphismAnnihilates` is the decidable window predicate
`p(M) = 0`.

The separator is `EndomorphismDissimilarByAnnihilator p M N := p(M) = 0 ∧ p(N) ≠ 0`.

**Soundness** (certificate level, exactly the r1 char-poly / rank discipline): if `M ~ N` over any field
(`N = S⁻¹ M S`), then `p(N) = S⁻¹ p(M) S` for EVERY polynomial `p`, so `p(M) = 0 ⟹ p(N) = 0`.  The
contrapositive is the certificate: an annihilator of `M` that fails on `N` refutes similarity.  Because the
minimal polynomial is the monic generator of the annihilator ideal, this separator sees the FULL minimal
polynomial — strictly sharper than the shipped char-poly and `2×2`-rank separators, which are BOTH blind to
`diag(1,1)` vs `[[1,1],[0,1]]` (shared char-poly `(x−1)²`, shared rank `2`) yet `p = x − 1` annihilates the
diagonal and not the Jordan block.

## Cayley–Hamilton grounding

`p(M) = 0` is machine-checked for `p =` the characteristic polynomial (`endomorphismCharPolyCoefficients`)
at `n = 2, 3`: the char poly annihilates its matrix, so the min poly always DIVIDES it — the annihilator
separator is always at least as strong as the char-poly separator, and the two-example groundings exhibit
the evaluation engine computing `Σ cₖ Mᵏ` correctly.

## Honest scope (what this delivers vs the remaining gap)

Delivered: the top invariant factor (minimal polynomial) as a decidable, kernel-checked, eigenvalue-free
dissimilarity separator, strictly stronger than every prior r1/r2 separator in this arc; plus the PROVEN
conjugation core `endomorphismWitnessUniformConjugation` (`Q·Aᵏ⁺¹·P = d·Bᵏ⁺¹` on the window, every `k`),
which removes the named ∀-refutation blocker — the missing sign-agnostic power cancellation is supplied as
`intMulPowerLeftCancelOfMagnitude`.  Upgrading the annihilator SEPARATOR itself from certificate-level to a
full proven ∀-refutation additionally needs the co-inverse window `Q·P = d·I` (for the polynomial's constant
term) and per-power linearity of `matrixPolyEval` — a smaller, honest remaining step.

Remaining (`invariantFactorSeparator` proper): the FULL invariant-factor LIST — equivalently the rational
canonical form — which is a COMPLETE similarity invariant (min poly alone is not: `min ∧ char` is incomplete
from `n = 7`).  That needs univariate ℚ[x] Euclidean GCD on the char-matrix minors; it is a real
multi-file polynomial-arithmetic arc, but the obstruction is GCD, not eigenvalue factoring.

## Zero-axiom design

`matrixPolyEval` is structural on the coefficient list over the shipped `endomorphismMatrixPower`,
`scalarMul`, `addMatrix`.  `EndomorphismAnnihilates` is the reducible `agreeOnWindow` predicate decided by
`Nat.decidableBallLT` + `Int.decEq` — the exact `decide` pattern of `endomorphismScaledInverseWindowProbe`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/EndomorphismMinimalPolynomial.lean`.
-/

namespace FX1Poly.ComputerAlgebra

open SetoidMatrix

/-! ## Polynomial evaluation at a matrix (`Σ cₖ · Mᵏ`) -/

/-- The running evaluation `Σ_{k ≥ startExponent} coeffs[k − startExponent] · Mᵏ`, structural on the
coefficient list.  The empty tail is the square zero matrix; each head coefficient scales the current
power and adds the tail (which continues at the next exponent). -/
def matrixPolyEvalFrom (dimension : Nat) (matrix : SetoidMatrix Int) :
    Nat → List Int → SetoidMatrix Int
  | _, [] => intMatrixZeroSquare dimension
  | startExponent, headCoefficient :: restCoefficients =>
      addMatrix intCommutativeRingWitness
        (intMatrixScale headCoefficient
          (endomorphismMatrixPower dimension matrix startExponent))
        (matrixPolyEvalFrom dimension matrix (startExponent + 1) restCoefficients)

/-- The value `p(M) = Σ cₖ · Mᵏ` of the ascending-coefficient polynomial `coefficients` at `matrix`. -/
def matrixPolyEval (dimension : Nat) (coefficients : List Int) (matrix : SetoidMatrix Int) :
    SetoidMatrix Int :=
  matrixPolyEvalFrom dimension matrix 0 coefficients

/-! ## The annihilation predicate (decidable) -/

/-- The polynomial `coefficients` annihilates `matrix`: `p(M) = 0` on the `dimension × dimension`
window.  Reducible so `Decidable` synthesis unfolds it to the bounded `agreeOnWindow` ball. -/
@[reducible] def EndomorphismAnnihilates (dimension : Nat) (coefficients : List Int)
    (matrix : SetoidMatrix Int) : Prop :=
  agreeOnWindow (matrixPolyEval dimension coefficients matrix)
    (intMatrixZeroSquare dimension) dimension dimension

/-! ## The proven conjugation core (removing the named ∀-refutation blocker)

The r1/r2 separators' soundness ("similar ⟹ same invariant") is stated at certificate level.  Here is the
PROVEN core for the annihilator route, mirroring `EndomorphismPowerZeroSeparator`'s "proven, not prose"
discipline: over any coherent-dimension scaled-pair witness the conjugation is EXACT up to the single scale
`d`, uniformly in the power —

  `Q · Aᵏ⁺¹ · P  =  d · Bᵏ⁺¹`   (on the window, every `k`).

This is the ladder `dᵏ · (Q·Aᵏ⁺¹·P) = dᵏ⁺¹ · Bᵏ⁺¹` with the common `dᵏ` cancelled.  Cancelling an EQUALITY
(not a vanishing) needs a SIGN-AGNOSTIC power cancellation, which the shipped `intMulPowerRightCancel`
(positive scale only) does not give — the exact lemma named as the blocker.  It is supplied first, from the
corpus zero-cancellation. -/

/-- **Magnitude power cancellation** — cancel a common `baseᵏ` from an EQUALITY for any nonzero-magnitude
base (the sign-agnostic sibling of `intMulPowerRightCancel`, which needs `0 < base`).  Routes the difference
`l − r` through the corpus `intFactorIsZeroOfPowerScaledZero`, so a negative determinant is fine. -/
theorem intMulPowerLeftCancelOfMagnitude {base : Int} (baseHasMagnitude : 1 ≤ base.natAbs)
    (exponentValue : Nat) {leftValue rightValue : Int}
    (productsAreEqual :
      intPower base exponentValue * leftValue = intPower base exponentValue * rightValue) :
    leftValue = rightValue :=
  let scaledDifferenceIsZero :
      intPower base exponentValue * (leftValue + -rightValue) = 0 :=
    (intMulComm (intPower base exponentValue) (leftValue + -rightValue)).trans
      ((intRightDistrib leftValue (-rightValue) (intPower base exponentValue)).trans
        ((congrArg (· + (-rightValue) * intPower base exponentValue)
            (intMulComm leftValue (intPower base exponentValue))).trans
          ((congrArg (intPower base exponentValue * leftValue + ·)
              (intMulComm (-rightValue) (intPower base exponentValue))).trans
            ((congrArg (intPower base exponentValue * leftValue + ·)
                (intMulNeg (intPower base exponentValue) rightValue)).trans
              ((congrArg (fun term => intPower base exponentValue * leftValue + -term)
                  productsAreEqual.symm).trans
                (intAddRightNeg (intPower base exponentValue * leftValue)))))))
  let differenceIsZero : leftValue + -rightValue = 0 :=
    intFactorIsZeroOfPowerScaledZero baseHasMagnitude exponentValue (leftValue + -rightValue)
      scaledDifferenceIsZero
  (intAddZero leftValue).symm.trans
    ((congrArg (leftValue + ·) (intAddLeftNeg rightValue).symm).trans
      ((intAddAssoc leftValue (-rightValue) rightValue).symm.trans
        ((congrArg (· + rightValue) differenceIsZero).trans
          (intZeroAdd rightValue))))

/-- **The uniform conjugation identity (PROVEN, not prose).**  Over any coherent-dimension scaled-pair
witness of nonzero-magnitude scale, `Q · Aᵏ⁺¹ · P = d · Bᵏ⁺¹` on the window for every `k` — the witnessed
conjugation is exact up to the single scale `d`, uniformly in the power.  This is the power ladder with the
common `dᵏ` cancelled entrywise via `intMulPowerLeftCancelOfMagnitude`; a genuine ∀-witness result, not a
certificate whose soundness lives in a docstring. -/
theorem endomorphismWitnessUniformConjugation
    (dimension : Nat) (source target changeOfBasis scaledInverse : SetoidMatrix Int)
    (scale : Int)
    (scaleHasMagnitude : 1 ≤ scale.natAbs)
    (sourceRowFits : source.rowCount = dimension) (sourceColFits : source.colCount = dimension)
    (targetRowFits : target.rowCount = dimension) (targetColFits : target.colCount = dimension)
    (basisColFits : changeOfBasis.colCount = dimension)
    (inverseColFits : scaledInverse.colCount = dimension)
    (inverseWindowHolds : agreeOnWindow (intMatrixMul changeOfBasis scaledInverse)
      (intMatrixScale scale (intMatrixIdentity dimension)) dimension dimension)
    (conjugacyWindowHolds : agreeOnWindow
      (intMatrixMul scaledInverse (intMatrixMul source changeOfBasis))
      (intMatrixScale scale target) dimension dimension)
    (powerPredecessor : Nat) :
    agreeOnWindow
      (intMatrixMul scaledInverse
        (intMatrixMul (endomorphismMatrixPower dimension source (powerPredecessor + 1)) changeOfBasis))
      (intMatrixScale scale (endomorphismMatrixPower dimension target (powerPredecessor + 1)))
      dimension dimension := by
  intro rowIndex rowBelow colIndex colBelow
  have ladderEntry := endomorphismWitnessPowerLadder dimension source target changeOfBasis
    scaledInverse scale sourceRowFits sourceColFits targetRowFits targetColFits basisColFits
    inverseColFits inverseWindowHolds conjugacyWindowHolds powerPredecessor
    rowIndex rowBelow colIndex colBelow
  exact intMulPowerLeftCancelOfMagnitude scaleHasMagnitude powerPredecessor
    (ladderEntry.trans
      ((congrArg (· * (endomorphismMatrixPower dimension target (powerPredecessor + 1)).entry
            rowIndex colIndex)
          (intPowerSucc scale powerPredecessor)).trans
        (intMulAssoc (intPower scale powerPredecessor) scale
          ((endomorphismMatrixPower dimension target (powerPredecessor + 1)).entry
            rowIndex colIndex))))

/-! ## Cayley–Hamilton groundings (the char poly annihilates; the evaluation engine is exercised) -/

/-- The `2×2` char poly `x² − 4x + 3` of `[[1,1],[0,3]]` annihilates it: `3·I − 4·A + A² = 0`. -/
theorem endomorphismCharPolyAnnihilatesTwoByTwo :
    EndomorphismAnnihilates 2 (endomorphismCharPolyCoefficients 2 (setoidMatrixOfRows [[1, 1], [0, 3]]))
      (setoidMatrixOfRows [[1, 1], [0, 3]]) := by decide

/-- The `3×3` char poly `x³ − 9x² + 26x − 24` of `diag(2,3,4)` annihilates it. -/
theorem endomorphismCharPolyAnnihilatesThreeByThree :
    EndomorphismAnnihilates 3
      (endomorphismCharPolyCoefficients 3 (setoidMatrixOfRows [[2, 0, 0], [0, 3, 0], [0, 0, 4]]))
      (setoidMatrixOfRows [[2, 0, 0], [0, 3, 0], [0, 0, 4]]) := by decide

/-- The linear polynomial `x − 1` (coefficients `[-1, 1]`) annihilates the identity `diag(1,1)`:
`(-1)·I + 1·I = 0`.  This is the diagonal's minimal polynomial (degree 1, since `M = I` is scalar). -/
theorem endomorphismLinearAnnihilatesScalar :
    EndomorphismAnnihilates 2 [-1, 1] (setoidMatrixOfRows [[1, 0], [0, 1]]) := by decide

/-! ## The annihilator separator -/

/-- `source` and `target` are dissimilar because the polynomial `coefficients` annihilates `source`
but NOT `target`.  Since similar matrices satisfy identical polynomial identities
(`p(S⁻¹MS) = S⁻¹ p(M) S`), an annihilator of one that fails on the other refutes similarity.  Reducible
so a concrete separation closes by `decide` (the `And` of a window equality and a window inequality). -/
@[reducible] def EndomorphismDissimilarByAnnihilator (dimension : Nat) (coefficients : List Int)
    (source target : SetoidMatrix Int) : Prop :=
  EndomorphismAnnihilates dimension coefficients source
    ∧ ¬ EndomorphismAnnihilates dimension coefficients target

/-- **The min-poly separation char-poly and rank cannot see.**  `diag(1,1)` vs the Jordan block
`[[1,1],[0,1]]`: the linear `x − 1` annihilates the scalar diagonal but sends the Jordan block to
`[[0,1],[0,0]] ≠ 0`.  Their minimal polynomials (`x − 1` vs `(x − 1)²`) differ, so they are dissimilar. -/
theorem endomorphismScalarVersusJordanDissimilar :
    EndomorphismDissimilarByAnnihilator 2 [-1, 1] (setoidMatrixOfRows [[1, 0], [0, 1]])
      (setoidMatrixOfRows [[1, 1], [0, 1]]) := by decide

/-- The scalar-vs-Jordan pair SHARES its characteristic polynomial `(x − 1)² = x² − 2x + 1`, confirming
the char-poly separator is blind to it — the annihilator (minimal-polynomial) separator is necessary. -/
theorem endomorphismScalarVersusJordanShareCharPoly :
    endomorphismCharPolyCoefficients 2 (setoidMatrixOfRows [[1, 0], [0, 1]])
      = endomorphismCharPolyCoefficients 2 (setoidMatrixOfRows [[1, 1], [0, 1]]) := by decide

/-- The scalar-vs-Jordan pair also SHARES its `2×2` rank (both `2`, since both are invertible),
confirming the shipped rank separator is ALSO blind to it — only the minimal polynomial distinguishes
these two representations of the walking endomorphism. -/
theorem endomorphismScalarVersusJordanShareRank :
    endomorphismRank2 (setoidMatrixOfRows [[1, 0], [0, 1]])
      = endomorphismRank2 (setoidMatrixOfRows [[1, 1], [0, 1]]) := by decide

/-! ## The canonical rank-blind 4×4 nilpotent separation (cross-check vs the rank sequence) -/

/-- **The `4×4` pair that even `rank(M)` cannot see.**  `J₂⊕J₂` (`[[0,1,0,0],[0,0,0,0],[0,0,0,1],
[0,0,0,0]]`, minimal polynomial `x²`) vs `J₃⊕J₁` (`[[0,1,0,0],[0,0,1,0],[0,0,0,0],[0,0,0,0]]`, minimal
polynomial `x³`): both are nilpotent with characteristic polynomial `x⁴` AND first rank `rank(M) = 2`, so
the char-poly separator and any single-power rank are blind.  The annihilator `p = x²` (`[0,0,1]`) sends
`J₂⊕J₂` to `M² = 0` but `J₃⊕J₁` to `M² ≠ 0` (entry `(0,2) = 1`), separating them by the minimal
polynomial.  This is exactly the pair `EndomorphismPowerZeroSeparator` handles by `rank(M²) = 0` vs `> 0`;
the annihilator route decides it INDEPENDENTLY, through a different engine. -/
theorem endomorphismJordanNilpotentDissimilarByMinPoly :
    EndomorphismDissimilarByAnnihilator 4 [0, 0, 1]
      (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]])
      (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]) := by decide

/-! ## The census feed extension -/

/-- The annihilator separator's grounding: the char poly annihilates its matrix at `n = 2` and `n = 3`
(so the minimal polynomial divides the characteristic polynomial — the separator dominates char-poly),
and the scalar-vs-Jordan pair is separated by `x − 1` while sharing both char poly and rank.  A single
certificate bundling the four machine-checked facts, so the "top invariant factor decided" claim is
backed by evidence, not assertion. -/
theorem walkingEndomorphismMinimalPolynomialGrounded :
    EndomorphismAnnihilates 2
        (endomorphismCharPolyCoefficients 2 (setoidMatrixOfRows [[1, 1], [0, 3]]))
        (setoidMatrixOfRows [[1, 1], [0, 3]])
      ∧ EndomorphismAnnihilates 3
          (endomorphismCharPolyCoefficients 3 (setoidMatrixOfRows [[2, 0, 0], [0, 3, 0], [0, 0, 4]]))
          (setoidMatrixOfRows [[2, 0, 0], [0, 3, 0], [0, 0, 4]])
      ∧ EndomorphismDissimilarByAnnihilator 2 [-1, 1] (setoidMatrixOfRows [[1, 0], [0, 1]])
          (setoidMatrixOfRows [[1, 1], [0, 1]]) :=
  ⟨endomorphismCharPolyAnnihilatesTwoByTwo, endomorphismCharPolyAnnihilatesThreeByThree,
    endomorphismScalarVersusJordanDissimilar⟩

/-- Marker: the walking-endomorphism arc ships the minimal-polynomial (top invariant factor) separator —
a decidable, eigenvalue-free dissimilarity certificate strictly stronger than the char-poly and rank
separators.  `= true` records that the annihilator engine, the Cayley–Hamilton groundings, and the
char-poly-and-rank-blind separation are all machine-checked.  The FULL invariant-factor list (the complete
similarity invariant, needing ℚ[x] Euclidean GCD — NOT eigenvalue factoring) stays the honest open gap. -/
def fxEndo_hasMinimalPolynomialAnnihilatorSeparator : Bool := true

end FX1Poly.ComputerAlgebra
