import FX1Poly.ComputerAlgebra.Algebra.SetoidRingTower

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SetoidMatrix — matrices over a setoid commutative ring

The generic matrix carrier of the `ComputerAlgebra/LinearAlgebra/` layer, parameterized ONCE over
`CommutativeRingWitness carrier` (the setoid-relative ring interface shipped in
`Number/ComplexReal.lean`).  Matrix-over-ℤ/ℚ/ℝ/ℂ are then four applications of the SAME laws — the
widenings induce matrix functors for free.

## Representation and setoid equality

A matrix is a pair of `Nat` dimensions plus a TOTAL entry function `Nat → Nat → carrier` (mathlib's
`m → n → R` shape, but `Nat`-indexed so there is no `Fin` elimination — every propext trap on
indexed matches is dodged, exactly as the concrete `IntMatrix` dodges them with extrinsic `List`
shape).  Two matrices `DenoteSame` (relative to a ring witness) when their dimensions agree and
their entries agree pointwise under the ring's own setoid `denotesSame` — so matrix equality is
built from the base setoid with NO funext (functions are never compared extensionally; only their
values at each index are, via the ring congruences).

## Zero-axiom design

  * Entry function is total; `DenoteSame` compares entries at every `(rowIndex, colIndex)` under the
    base setoid, never by funext.
  * `identityMatrix` uses `if rowIndex = colIndex` on `Nat.decEq` (structural), discharged by the
    axiom-free `if_pos`/`if_neg`.
  * Every additive/scalar/transpose law is pointwise: it reduces to a single base-ring congruence or
    law applied under `entriesAgree`.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SetoidMatrix.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-- A matrix over `carrier`: two `Nat` dimensions plus a total entry function.  Shape is intrinsic
in the two fields; the entry function is total, reading a canonical value off-window. -/
structure SetoidMatrix (carrier : Type) where
  rowCount : Nat
  colCount : Nat
  entry : Nat → Nat → carrier

namespace SetoidMatrix

/-! ## Setoid equality relative to a ring witness -/

/-- Two matrices denote the same value over `ring`: equal dimensions and pointwise-equal entries
under the base setoid.  The entry agreement is stated at EVERY index (the ops build entries
uniformly, so pointwise-everywhere is both true and the cheapest to prove). -/
structure DenoteSame {carrier : Type} (ring : CommutativeRingWitness carrier)
    (leftMatrix rightMatrix : SetoidMatrix carrier) : Prop where
  sameRowCount : leftMatrix.rowCount = rightMatrix.rowCount
  sameColCount : leftMatrix.colCount = rightMatrix.colCount
  entriesAgree :
    ∀ rowIndex colIndex : Nat,
      ring.denotesSame (leftMatrix.entry rowIndex colIndex) (rightMatrix.entry rowIndex colIndex)

/-- Reflexivity of matrix sameness — from the base setoid's reflexivity, pointwise. -/
theorem denoteSameRefl {carrier : Type} (ring : CommutativeRingWitness carrier)
    (matrix : SetoidMatrix carrier) : DenoteSame ring matrix matrix :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      ring.denotesSameIsReflexive (matrix.entry rowIndex colIndex) }

/-- Symmetry of matrix sameness. -/
theorem denoteSameSymm {carrier : Type} (ring : CommutativeRingWitness carrier)
    {leftMatrix rightMatrix : SetoidMatrix carrier}
    (areSame : DenoteSame ring leftMatrix rightMatrix) : DenoteSame ring rightMatrix leftMatrix :=
  { sameRowCount := Eq.symm areSame.sameRowCount
    sameColCount := Eq.symm areSame.sameColCount
    entriesAgree := fun rowIndex colIndex =>
      ring.denotesSameIsSymmetric _ _ (areSame.entriesAgree rowIndex colIndex) }

/-- Transitivity of matrix sameness. -/
theorem denoteSameTrans {carrier : Type} (ring : CommutativeRingWitness carrier)
    {firstMatrix middleMatrix lastMatrix : SetoidMatrix carrier}
    (firstAgrees : DenoteSame ring firstMatrix middleMatrix)
    (lastAgrees : DenoteSame ring middleMatrix lastMatrix) :
    DenoteSame ring firstMatrix lastMatrix :=
  { sameRowCount := Eq.trans firstAgrees.sameRowCount lastAgrees.sameRowCount
    sameColCount := Eq.trans firstAgrees.sameColCount lastAgrees.sameColCount
    entriesAgree := fun rowIndex colIndex =>
      ring.denotesSameIsTransitive _ _ _
        (firstAgrees.entriesAgree rowIndex colIndex)
        (lastAgrees.entriesAgree rowIndex colIndex) }

/-! ## The core operations -/

/-- The all-zero matrix of the given dimensions. -/
def zeroMatrix {carrier : Type} (ring : CommutativeRingWitness carrier)
    (rows cols : Nat) : SetoidMatrix carrier :=
  { rowCount := rows, colCount := cols, entry := fun _ _ => ring.zero }

/-- The identity matrix: `one` on the diagonal, `zero` off it. -/
def identityMatrix {carrier : Type} (ring : CommutativeRingWitness carrier)
    (dimension : Nat) : SetoidMatrix carrier :=
  { rowCount := dimension, colCount := dimension,
    entry := fun rowIndex colIndex => if rowIndex = colIndex then ring.one else ring.zero }

/-- Entrywise sum (dimensions taken from the left operand; well-behaved when the shapes agree). -/
def addMatrix {carrier : Type} (ring : CommutativeRingWitness carrier)
    (leftMatrix rightMatrix : SetoidMatrix carrier) : SetoidMatrix carrier :=
  { rowCount := leftMatrix.rowCount, colCount := leftMatrix.colCount,
    entry := fun rowIndex colIndex =>
      ring.add (leftMatrix.entry rowIndex colIndex) (rightMatrix.entry rowIndex colIndex) }

/-- Entrywise negation. -/
def negMatrix {carrier : Type} (ring : CommutativeRingWitness carrier)
    (matrix : SetoidMatrix carrier) : SetoidMatrix carrier :=
  { rowCount := matrix.rowCount, colCount := matrix.colCount,
    entry := fun rowIndex colIndex => ring.neg (matrix.entry rowIndex colIndex) }

/-- Entrywise difference `left - right := left + (neg right)`. -/
def subMatrix {carrier : Type} (ring : CommutativeRingWitness carrier)
    (leftMatrix rightMatrix : SetoidMatrix carrier) : SetoidMatrix carrier :=
  addMatrix ring leftMatrix (negMatrix ring rightMatrix)

/-- Left scalar multiplication: `scalar * entry` in every cell. -/
def scalarMul {carrier : Type} (ring : CommutativeRingWitness carrier)
    (scalar : carrier) (matrix : SetoidMatrix carrier) : SetoidMatrix carrier :=
  { rowCount := matrix.rowCount, colCount := matrix.colCount,
    entry := fun rowIndex colIndex => ring.mul scalar (matrix.entry rowIndex colIndex) }

/-- Transpose: swap the dimensions and read `entry j i`. -/
def transposeMatrix {carrier : Type} (matrix : SetoidMatrix carrier) : SetoidMatrix carrier :=
  { rowCount := matrix.colCount, colCount := matrix.rowCount,
    entry := fun rowIndex colIndex => matrix.entry colIndex rowIndex }

/-! ## Congruences (setoid-respecting operations) -/

/-- Addition respects the setoid on both arguments. -/
theorem addMatrixRespectsDenoteSame {carrier : Type} (ring : CommutativeRingWitness carrier)
    {leftMatrix newLeftMatrix rightMatrix newRightMatrix : SetoidMatrix carrier}
    (leftAgrees : DenoteSame ring leftMatrix newLeftMatrix)
    (rightAgrees : DenoteSame ring rightMatrix newRightMatrix) :
    DenoteSame ring (addMatrix ring leftMatrix rightMatrix)
      (addMatrix ring newLeftMatrix newRightMatrix) :=
  { sameRowCount := leftAgrees.sameRowCount
    sameColCount := leftAgrees.sameColCount
    entriesAgree := fun rowIndex colIndex =>
      ring.addRespectsDenotesSame _ _ _ _
        (leftAgrees.entriesAgree rowIndex colIndex)
        (rightAgrees.entriesAgree rowIndex colIndex) }

/-- Negation respects the setoid. -/
theorem negMatrixRespectsDenoteSame {carrier : Type} (ring : CommutativeRingWitness carrier)
    {leftMatrix rightMatrix : SetoidMatrix carrier}
    (areSame : DenoteSame ring leftMatrix rightMatrix) :
    DenoteSame ring (negMatrix ring leftMatrix) (negMatrix ring rightMatrix) :=
  { sameRowCount := areSame.sameRowCount
    sameColCount := areSame.sameColCount
    entriesAgree := fun rowIndex colIndex =>
      ring.negRespectsDenotesSame _ _ (areSame.entriesAgree rowIndex colIndex) }

/-- Difference respects the setoid on both arguments. -/
theorem subMatrixRespectsDenoteSame {carrier : Type} (ring : CommutativeRingWitness carrier)
    {leftMatrix newLeftMatrix rightMatrix newRightMatrix : SetoidMatrix carrier}
    (leftAgrees : DenoteSame ring leftMatrix newLeftMatrix)
    (rightAgrees : DenoteSame ring rightMatrix newRightMatrix) :
    DenoteSame ring (subMatrix ring leftMatrix rightMatrix)
      (subMatrix ring newLeftMatrix newRightMatrix) :=
  addMatrixRespectsDenoteSame ring leftAgrees (negMatrixRespectsDenoteSame ring rightAgrees)

/-- Scalar multiplication respects the setoid on both the scalar and the matrix. -/
theorem scalarMulRespectsDenoteSame {carrier : Type} (ring : CommutativeRingWitness carrier)
    {leftScalar rightScalar : carrier} {leftMatrix rightMatrix : SetoidMatrix carrier}
    (scalarAgrees : ring.denotesSame leftScalar rightScalar)
    (matrixAgrees : DenoteSame ring leftMatrix rightMatrix) :
    DenoteSame ring (scalarMul ring leftScalar leftMatrix)
      (scalarMul ring rightScalar rightMatrix) :=
  { sameRowCount := matrixAgrees.sameRowCount
    sameColCount := matrixAgrees.sameColCount
    entriesAgree := fun rowIndex colIndex =>
      ring.mulRespectsDenotesSame _ _ _ _ scalarAgrees
        (matrixAgrees.entriesAgree rowIndex colIndex) }

/-- Transpose respects the setoid. -/
theorem transposeMatrixRespectsDenoteSame {carrier : Type} (ring : CommutativeRingWitness carrier)
    {leftMatrix rightMatrix : SetoidMatrix carrier}
    (areSame : DenoteSame ring leftMatrix rightMatrix) :
    DenoteSame ring (transposeMatrix leftMatrix) (transposeMatrix rightMatrix) :=
  { sameRowCount := areSame.sameColCount
    sameColCount := areSame.sameRowCount
    entriesAgree := fun rowIndex colIndex => areSame.entriesAgree colIndex rowIndex }

/-! ## The additive abelian-group laws -/

/-- Addition is commutative (dimensions must agree — matrix addition is only a total operation on a
fixed shape). -/
theorem addMatrixComm {carrier : Type} (ring : CommutativeRingWitness carrier)
    (leftMatrix rightMatrix : SetoidMatrix carrier)
    (rowMatch : leftMatrix.rowCount = rightMatrix.rowCount)
    (colMatch : leftMatrix.colCount = rightMatrix.colCount) :
    DenoteSame ring (addMatrix ring leftMatrix rightMatrix)
      (addMatrix ring rightMatrix leftMatrix) :=
  { sameRowCount := rowMatch
    sameColCount := colMatch
    entriesAgree := fun rowIndex colIndex =>
      ring.addIsCommutative (leftMatrix.entry rowIndex colIndex)
        (rightMatrix.entry rowIndex colIndex) }

/-- Addition is associative — dimensions align by construction (both sides carry the left-most
operand's shape), so no shape hypothesis is needed. -/
theorem addMatrixAssoc {carrier : Type} (ring : CommutativeRingWitness carrier)
    (firstMatrix secondMatrix thirdMatrix : SetoidMatrix carrier) :
    DenoteSame ring (addMatrix ring (addMatrix ring firstMatrix secondMatrix) thirdMatrix)
      (addMatrix ring firstMatrix (addMatrix ring secondMatrix thirdMatrix)) :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      ring.addIsAssociative (firstMatrix.entry rowIndex colIndex)
        (secondMatrix.entry rowIndex colIndex) (thirdMatrix.entry rowIndex colIndex) }

/-- The zero matrix of matching shape is a right additive identity. -/
theorem addMatrixZeroRight {carrier : Type} (ring : CommutativeRingWitness carrier)
    (matrix : SetoidMatrix carrier) :
    DenoteSame ring (addMatrix ring matrix (zeroMatrix ring matrix.rowCount matrix.colCount))
      matrix :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      ring.zeroIsRightAdditiveIdentity (matrix.entry rowIndex colIndex) }

/-- Negation is a right additive inverse. -/
theorem addMatrixNegRight {carrier : Type} (ring : CommutativeRingWitness carrier)
    (matrix : SetoidMatrix carrier) :
    DenoteSame ring (addMatrix ring matrix (negMatrix ring matrix))
      (zeroMatrix ring matrix.rowCount matrix.colCount) :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      ring.negIsRightAdditiveInverse (matrix.entry rowIndex colIndex) }

/-- Subtracting a matrix from itself yields the zero matrix. -/
theorem subMatrixSelf {carrier : Type} (ring : CommutativeRingWitness carrier)
    (matrix : SetoidMatrix carrier) :
    DenoteSame ring (subMatrix ring matrix matrix)
      (zeroMatrix ring matrix.rowCount matrix.colCount) :=
  addMatrixNegRight ring matrix

/-! ## Scalar-multiplication laws -/

/-- Scalar multiplication distributes over matrix addition. -/
theorem scalarMulDistributesOverAdd {carrier : Type} (ring : CommutativeRingWitness carrier)
    (scalar : carrier) (leftMatrix rightMatrix : SetoidMatrix carrier) :
    DenoteSame ring (scalarMul ring scalar (addMatrix ring leftMatrix rightMatrix))
      (addMatrix ring (scalarMul ring scalar leftMatrix) (scalarMul ring scalar rightMatrix)) :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      ring.mulDistributesOverAdd scalar (leftMatrix.entry rowIndex colIndex)
        (rightMatrix.entry rowIndex colIndex) }

/-- Multiplying by `one` leaves a matrix unchanged (up to the setoid). -/
theorem scalarMulOne {carrier : Type} (ring : CommutativeRingWitness carrier)
    (matrix : SetoidMatrix carrier) :
    DenoteSame ring (scalarMul ring ring.one matrix) matrix :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      ring.denotesSameIsTransitive _ _ _
        (ring.mulIsCommutative ring.one (matrix.entry rowIndex colIndex))
        (ring.oneIsRightMultiplicativeIdentity (matrix.entry rowIndex colIndex)) }

/-! ## Transpose laws -/

/-- Transpose is involutive. -/
theorem transposeMatrixInvolutive {carrier : Type} (ring : CommutativeRingWitness carrier)
    (matrix : SetoidMatrix carrier) :
    DenoteSame ring (transposeMatrix (transposeMatrix matrix)) matrix :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      ring.denotesSameIsReflexive (matrix.entry rowIndex colIndex) }

/-- Transpose of a sum is the sum of transposes. -/
theorem transposeMatrixOfAdd {carrier : Type} (ring : CommutativeRingWitness carrier)
    (leftMatrix rightMatrix : SetoidMatrix carrier) :
    DenoteSame ring (transposeMatrix (addMatrix ring leftMatrix rightMatrix))
      (addMatrix ring (transposeMatrix leftMatrix) (transposeMatrix rightMatrix)) :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      ring.denotesSameIsReflexive
        (ring.add (leftMatrix.entry colIndex rowIndex) (rightMatrix.entry colIndex rowIndex)) }

/-- The transpose of the identity matrix is the identity matrix. -/
theorem transposeIdentityMatrix {carrier : Type} (ring : CommutativeRingWitness carrier)
    (dimension : Nat) :
    DenoteSame ring (transposeMatrix (identityMatrix ring dimension))
      (identityMatrix ring dimension) :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      match Nat.decEq rowIndex colIndex with
      | isTrue isDiagonal => by
          dsimp only [transposeMatrix, identityMatrix]
          rw [if_pos (Eq.symm isDiagonal), if_pos isDiagonal]
          exact ring.denotesSameIsReflexive ring.one
      | isFalse isOffDiagonal => by
          dsimp only [transposeMatrix, identityMatrix]
          rw [if_neg (fun isSwappedDiagonal => isOffDiagonal (Eq.symm isSwappedDiagonal)),
            if_neg isOffDiagonal]
          exact ring.denotesSameIsReflexive ring.zero }

end SetoidMatrix

end FX1Poly.ComputerAlgebra
