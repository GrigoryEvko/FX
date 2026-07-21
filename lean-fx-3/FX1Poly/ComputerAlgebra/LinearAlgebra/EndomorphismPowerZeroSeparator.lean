import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismSimilarity
import FX1Poly.ComputerAlgebra.Number.IntPower
import FX1Poly.ComputerAlgebra.Number.IntCancellation
import FX1Poly.ComputerAlgebra.Number.IntNegation

/-! # EndomorphismPowerZeroSeparator — the rank-sequence separator at its rank-zero boundary

`EndomorphismSimilarity` named `rankSequenceNilpotent` as a wall: the complete nilpotent similarity
separator is the rank sequence `rank(M^k)`, which needs matrix powers.  This file ships the matrix power
(structural iterate of the shipped `mulMatrix`) and the proven fragment of the separator: the rank-`0`
boundary `rank(M^k) = 0` vs `> 0`, i.e. the `k`-th power vanishing on the window vs not.

## The proven invariance direction

Unlike separators whose "similar ⟹ equal invariant" backing is prose, the zero-pattern direction is
machine-proved here, in three theorems over an arbitrary coherent-dimension scaled-pair witness:

  * `endomorphismWitnessPowerLadder` — from `P·Q = d·I` and `Q·(A·P) = d·B` on the window follows
    `d^k · (Q·(A^(k+1)·P)) = d^(k+1) · B^(k+1)`, for every `k`, by induction with no division and no
    cancellation (the scale is carried, never cancelled);
  * `endomorphismWitnessTransportsPowerVanishing` — if `A^(k+1)` vanishes on the window, so does
    `B^(k+1)` (cancel the nonzero `d`-power entrywise via the corpus zero-product lemma);
  * `endomorphismWitnessReflectsPowerVanishing` — conversely, if `B^(k+1)` vanishes then so does
    `A^(k+1)`, by the sandwich `(P·Q)·A^(k+1)·(P·Q) = d²·A^(k+1)`.

Hence `EndomorphismDissimilarByRankSequence` (either power vanishes while the other survives) is a
genuine ∀-witness refutation: no change of basis, scaled inverse, or scale can witness the pair.

## The dimension-junk forgery (a checker gap, repaired additively)

`WitnessesSimilarity` does not constrain the `changeOfBasis`/`scaledInverse` dimension fields, and its
window sums range over the operands' intrinsic `colCount` fields.  A forged witness with off-dimension
`P`/`Q` passes the raw checker against the machine-checked dissimilar pair `[[1,0],[0,0]]` vs
`[[2,0],[0,0]]` (`endomorphismDimensionForgeryPassesRawChecker`: `P` is `2×3`, `Q` is `3×2`, the phantom
third column/row cancels inside `P·Q` but is invisible to `Q·(A·P)`).  The additive repair
`WitnessesSimilarityWithCoherentDimensions` — the raw checker plus eight dimension-coherence equations —
rejects the forgery (`endomorphismDimensionForgeryRejectedWithCoherence`) and is the hypothesis of every
refutation theorem here; the shipped witnesses satisfy it by `rfl`.

## Honest scope

The graded rank values (`rank(M^k) = r > 0`) need the general minor selector; the general "unequal rank
sequences ⟹ dissimilar" for nonzero ranks would additionally need Cauchy–Binet and stays
certificate-level.  The rank-0 boundary already separates the canonical rank-blind pair: the `4×4`
nilpotents `J2⊕J2` vs `J3⊕J1` share the characteristic polynomial `x^4` and the first rank, differing
exactly at `rank(M²) = 0` vs `1`.

## Zero-axiom design

All matrix algebra is routed through the shipped `CommutativeRingWitness` law fields and the `sumUpTo`
toolkit; the only new Int lemmas are the zero-product cancellations, derived from the corpus
`intEqZeroOfMulOfNatSuccEqZero` by constructor cases.  The matrix power is structural on the exponent.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`; gated per
declaration in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

open SetoidMatrix

/-! ## Reducible Int-matrix operation aliases (decide-transparent) -/

/-- Integer matrix multiplication (the shipped `mulMatrix` at the ℤ witness). -/
@[reducible] def intMatrixMul (leftMatrix rightMatrix : SetoidMatrix Int) : SetoidMatrix Int :=
  mulMatrix intCommutativeRingWitness leftMatrix rightMatrix

/-- Integer scalar multiplication of a matrix. -/
@[reducible] def intMatrixScale (scaleValue : Int) (matrix : SetoidMatrix Int) : SetoidMatrix Int :=
  scalarMul intCommutativeRingWitness scaleValue matrix

/-- The integer identity matrix. -/
@[reducible] def intMatrixIdentity (dimension : Nat) : SetoidMatrix Int :=
  identityMatrix intCommutativeRingWitness dimension

/-- The square integer zero matrix. -/
@[reducible] def intMatrixZeroSquare (dimension : Nat) : SetoidMatrix Int :=
  zeroMatrix intCommutativeRingWitness dimension dimension

/-- The ℤ ring witness setoid is definitional equality; this bridge converts once and for all. -/
theorem intDenotesSameIsEq {leftValue rightValue : Int}
    (areSame : intCommutativeRingWitness.denotesSame leftValue rightValue) :
    leftValue = rightValue :=
  areSame

/-! ## The matrix power (structural on the exponent) -/

/-- The `exponent`-th power of a square integer matrix at the given `dimension`, defined as the
structural iterate of the shipped `mulMatrix` with the identity seed: `M^0 = I`,
`M^(k+1) = M^k · M`. -/
def endomorphismMatrixPower (dimension : Nat) (matrix : SetoidMatrix Int) :
    Nat → SetoidMatrix Int
  | 0 => intMatrixIdentity dimension
  | Nat.succ exponentValue =>
      intMatrixMul (endomorphismMatrixPower dimension matrix exponentValue) matrix

/-- Every power has row count `dimension` (the seed does, and `mulMatrix` keeps the left row
count). -/
theorem endomorphismMatrixPowerRowCount (dimension : Nat) (matrix : SetoidMatrix Int) :
    ∀ exponentValue : Nat,
      (endomorphismMatrixPower dimension matrix exponentValue).rowCount = dimension
  | 0 => rfl
  | Nat.succ exponentValue => endomorphismMatrixPowerRowCount dimension matrix exponentValue

/-- A positive power has the base matrix's column count (definitional). -/
theorem endomorphismMatrixPowerSuccColCount (dimension : Nat) (matrix : SetoidMatrix Int)
    (exponentValue : Nat) :
    (endomorphismMatrixPower dimension matrix (exponentValue + 1)).colCount = matrix.colCount :=
  rfl

/-! ## Zero-product cancellation over ℤ (from the corpus, no `natAbs`-multiplicativity needed) -/

/-- A product with a magnitude-`≥ 1` left factor vanishes only if the right factor does.
Constructor cases on the scale route everything through the corpus
`intEqZeroOfMulOfNatSuccEqZero`. -/
theorem intFactorIsZeroOfScaledZero : ∀ {scaleValue : Int}, ∀ (value : Int),
    1 ≤ scaleValue.natAbs → scaleValue * value = 0 → value = 0
  | Int.ofNat 0, _, scaleHasMagnitude, _ =>
      absurd scaleHasMagnitude (Nat.not_succ_le_zero 0)
  | Int.ofNat (Nat.succ scalePredecessor), value, _, productIsZero =>
      have valueScaleZero : value * Int.ofNat (Nat.succ scalePredecessor) = 0 :=
        (intMulComm value (Int.ofNat (Nat.succ scalePredecessor))).trans productIsZero
      -- The cancellation corpus phrases the positive scale as `1 + n`; `Nat.succ n = n + 1`
      -- definitionally, so one clean `Nat.add_comm` bridges to `1 + n` (no propext).
      intEqZeroOfMulOfNatSuccEqZero value scalePredecessor
        ((congrArg (fun exponent => value * Int.ofNat exponent)
            (Nat.add_comm scalePredecessor 1)).symm.trans valueScaleZero)
  | Int.negSucc scalePredecessor, value, _, productIsZero =>
      have swappedIsZero : value * Int.negSucc scalePredecessor = 0 :=
        (intMulComm value (Int.negSucc scalePredecessor)).trans productIsZero
      have negatedIsZero : -(value * Int.ofNat (Nat.succ scalePredecessor)) = 0 :=
        (intMulNeg value (Int.ofNat (Nat.succ scalePredecessor))).symm.trans swappedIsZero
      have positiveProductIsZero : value * Int.ofNat (Nat.succ scalePredecessor) = 0 :=
        (intNegNeg (value * Int.ofNat (Nat.succ scalePredecessor))).symm.trans
          ((congrArg Int.neg negatedIsZero).trans intNegZero)
      intEqZeroOfMulOfNatSuccEqZero value scalePredecessor
        ((congrArg (fun exponent => value * Int.ofNat exponent)
            (Nat.add_comm scalePredecessor 1)).symm.trans positiveProductIsZero)

/-- Iterated cancellation: a product with an `intPower` of a magnitude-`≥ 1` base vanishes only if
the co-factor does.  Structural on the exponent — each step peels one base factor via
`intMulAssoc` and cancels it. -/
theorem intFactorIsZeroOfPowerScaledZero {base : Int} (baseHasMagnitude : 1 ≤ base.natAbs) :
    ∀ (exponentValue : Nat) (value : Int), intPower base exponentValue * value = 0 → value = 0
  | 0, value, productIsZero => (intOneMul value).symm.trans productIsZero
  | Nat.succ exponentValue, value, productIsZero =>
      have reassociatedIsZero : intPower base exponentValue * (base * value) = 0 :=
        (intMulAssoc (intPower base exponentValue) base value).symm.trans productIsZero
      intFactorIsZeroOfScaledZero value baseHasMagnitude
        (intFactorIsZeroOfPowerScaledZero baseHasMagnitude exponentValue (base * value)
          reassociatedIsZero)

/-! ## The windowed-equality calculus over ℤ

`agreeOnWindow` compares entries inside the `n × n` window; the multiplication sums range over the
operands' intrinsic `colCount` fields, so every congruence below carries the column-count side
conditions that keep all reads in-window. -/

/-- Window agreement is reflexive. -/
theorem agreeOnWindowRefl (matrix : SetoidMatrix Int) (height width : Nat) :
    agreeOnWindow matrix matrix height width :=
  fun _ _ _ _ => rfl

/-- Window agreement is symmetric. -/
theorem agreeOnWindowSymm {leftMatrix rightMatrix : SetoidMatrix Int} {height width : Nat}
    (agree : agreeOnWindow leftMatrix rightMatrix height width) :
    agreeOnWindow rightMatrix leftMatrix height width :=
  fun rowIndex rowBelow colIndex colBelow => (agree rowIndex rowBelow colIndex colBelow).symm

/-- Window agreement is transitive. -/
theorem agreeOnWindowTrans {firstMatrix middleMatrix lastMatrix : SetoidMatrix Int}
    {height width : Nat}
    (firstAgrees : agreeOnWindow firstMatrix middleMatrix height width)
    (lastAgrees : agreeOnWindow middleMatrix lastMatrix height width) :
    agreeOnWindow firstMatrix lastMatrix height width :=
  fun rowIndex rowBelow colIndex colBelow =>
    (firstAgrees rowIndex rowBelow colIndex colBelow).trans
      (lastAgrees rowIndex rowBelow colIndex colBelow)

/-- Propositional matrix equality restricts to any window. -/
theorem agreeOnWindowOfEq {leftMatrix rightMatrix : SetoidMatrix Int}
    (areEqual : leftMatrix = rightMatrix) (height width : Nat) :
    agreeOnWindow leftMatrix rightMatrix height width :=
  areEqual ▸ agreeOnWindowRefl leftMatrix height width

/-- Multiplication is a window congruence in both factors, provided both left factors' column
counts equal the window size (so the sums range exactly over in-window inner indices). -/
theorem intMatrixMulCongrOnWindow (windowSize : Nat)
    {leftMatrix newLeftMatrix rightMatrix newRightMatrix : SetoidMatrix Int}
    (leftColFits : leftMatrix.colCount = windowSize)
    (newLeftColFits : newLeftMatrix.colCount = windowSize)
    (leftAgrees : agreeOnWindow leftMatrix newLeftMatrix windowSize windowSize)
    (rightAgrees : agreeOnWindow rightMatrix newRightMatrix windowSize windowSize) :
    agreeOnWindow (intMatrixMul leftMatrix rightMatrix)
      (intMatrixMul newLeftMatrix newRightMatrix) windowSize windowSize := by
  intro rowIndex rowBelow colIndex colBelow
  dsimp only [intMatrixMul, mulMatrix]
  rw [leftColFits, newLeftColFits]
  exact intDenotesSameIsEq (sumUpToCongr intCommutativeRingWitness windowSize
    (fun innerIndex innerBelow =>
      intCommutativeRingWitness.mulRespectsDenotesSame _ _ _ _
        (leftAgrees rowIndex rowBelow innerIndex innerBelow)
        (rightAgrees innerIndex innerBelow colIndex colBelow)))

/-- Associativity of matrix multiplication, restricted to a window (it holds at every index). -/
theorem intMatrixMulAssocOnWindow (firstMatrix secondMatrix thirdMatrix : SetoidMatrix Int)
    (height width : Nat) :
    agreeOnWindow (intMatrixMul (intMatrixMul firstMatrix secondMatrix) thirdMatrix)
      (intMatrixMul firstMatrix (intMatrixMul secondMatrix thirdMatrix)) height width :=
  fun rowIndex _ colIndex _ =>
    intDenotesSameIsEq
      ((mulMatrixAssoc intCommutativeRingWitness firstMatrix secondMatrix thirdMatrix).entriesAgree
        rowIndex colIndex)

/-- A left scalar pulls out of a product: `(c·X)·Y = c·(X·Y)` at every index. -/
theorem intMatrixScaleMulLeftOnWindow (scaleValue : Int)
    (leftMatrix rightMatrix : SetoidMatrix Int) (height width : Nat) :
    agreeOnWindow (intMatrixMul (intMatrixScale scaleValue leftMatrix) rightMatrix)
      (intMatrixScale scaleValue (intMatrixMul leftMatrix rightMatrix)) height width := by
  intro rowIndex rowBelow colIndex colBelow
  dsimp only [intMatrixMul, intMatrixScale, mulMatrix, scalarMul]
  exact intDenotesSameIsEq (intCommutativeRingWitness.denotesSameIsTransitive _ _ _
    (sumUpToCongr intCommutativeRingWitness leftMatrix.colCount
      (fun innerIndex _ =>
        intCommutativeRingWitness.mulIsAssociative scaleValue
          (leftMatrix.entry rowIndex innerIndex) (rightMatrix.entry innerIndex colIndex)))
    (sumUpToMulLeft intCommutativeRingWitness leftMatrix.colCount scaleValue
      (fun innerIndex =>
        intCommutativeRingWitness.mul (leftMatrix.entry rowIndex innerIndex)
          (rightMatrix.entry innerIndex colIndex))))

/-- The three-factor left commutation `a·(b·c) = b·(a·c)` over ℤ, from the witness laws. -/
theorem intMulLeftCommute (firstValue secondValue thirdValue : Int) :
    firstValue * (secondValue * thirdValue) = secondValue * (firstValue * thirdValue) :=
  (intMulAssoc firstValue secondValue thirdValue).symm.trans
    ((congrArg (· * thirdValue) (intMulComm firstValue secondValue)).trans
      (intMulAssoc secondValue firstValue thirdValue))

/-- A right scalar pulls out of a product: `X·(c·Y) = c·(X·Y)` at every index. -/
theorem intMatrixScaleMulRightOnWindow (scaleValue : Int)
    (leftMatrix rightMatrix : SetoidMatrix Int) (height width : Nat) :
    agreeOnWindow (intMatrixMul leftMatrix (intMatrixScale scaleValue rightMatrix))
      (intMatrixScale scaleValue (intMatrixMul leftMatrix rightMatrix)) height width := by
  intro rowIndex rowBelow colIndex colBelow
  dsimp only [intMatrixMul, intMatrixScale, mulMatrix, scalarMul]
  exact intDenotesSameIsEq (intCommutativeRingWitness.denotesSameIsTransitive _ _ _
    (sumUpToCongr intCommutativeRingWitness leftMatrix.colCount
      (fun innerIndex _ =>
        intMulLeftCommute (leftMatrix.entry rowIndex innerIndex) scaleValue
          (rightMatrix.entry innerIndex colIndex)))
    (sumUpToMulLeft intCommutativeRingWitness leftMatrix.colCount scaleValue
      (fun innerIndex =>
        intCommutativeRingWitness.mul (leftMatrix.entry rowIndex innerIndex)
          (rightMatrix.entry innerIndex colIndex))))

/-- Nested scalars collapse to their product: `c·(e·X) = (c·e)·X` at every index. -/
theorem intMatrixScaleCollapseOnWindow (outerScale innerScale : Int)
    (matrix : SetoidMatrix Int) (height width : Nat) :
    agreeOnWindow (intMatrixScale outerScale (intMatrixScale innerScale matrix))
      (intMatrixScale (outerScale * innerScale) matrix) height width :=
  fun rowIndex _ colIndex _ =>
    (intMulAssoc outerScale innerScale (matrix.entry rowIndex colIndex)).symm

/-- Scalar multiplication is a window congruence in the matrix argument. -/
theorem intMatrixScaleCongrOnWindow (scaleValue : Int)
    {leftMatrix rightMatrix : SetoidMatrix Int} {height width : Nat}
    (agree : agreeOnWindow leftMatrix rightMatrix height width) :
    agreeOnWindow (intMatrixScale scaleValue leftMatrix)
      (intMatrixScale scaleValue rightMatrix) height width :=
  fun rowIndex rowBelow colIndex colBelow =>
    congrArg (scaleValue * ·) (agree rowIndex rowBelow colIndex colBelow)

/-- Scaling by `1` is the identity at every index. -/
theorem intMatrixScaleOneOnWindow (matrix : SetoidMatrix Int) (height width : Nat) :
    agreeOnWindow (intMatrixScale 1 matrix) matrix height width :=
  fun rowIndex _ colIndex _ => intOneMul (matrix.entry rowIndex colIndex)

/-- Left identity absorb on the window (needs the row count to match the window size). -/
theorem intMatrixMulIdentityLeftOnWindow (windowSize : Nat) {matrix : SetoidMatrix Int}
    (rowFits : matrix.rowCount = windowSize) :
    agreeOnWindow (intMatrixMul (intMatrixIdentity windowSize) matrix) matrix
      windowSize windowSize := by
  intro rowIndex rowBelow colIndex colBelow
  rw [← rowFits]
  exact intDenotesSameIsEq
    (mulMatrixIdentityLeftEntry intCommutativeRingWitness matrix rowIndex colIndex
      (rowFits ▸ rowBelow))

/-- Right identity absorb on the window (needs the column count to match the window size). -/
theorem intMatrixMulIdentityRightOnWindow (windowSize : Nat) {matrix : SetoidMatrix Int}
    (colFits : matrix.colCount = windowSize) :
    agreeOnWindow (intMatrixMul matrix (intMatrixIdentity windowSize)) matrix
      windowSize windowSize := by
  intro rowIndex rowBelow colIndex colBelow
  rw [← colFits]
  exact intDenotesSameIsEq
    (mulMatrixIdentityRightEntry intCommutativeRingWitness matrix rowIndex colIndex
      (colFits ▸ colBelow))

/-- A window-vanishing left factor kills the product on the window. -/
theorem intMatrixMulVanishingLeftFactorOnWindow (windowSize : Nat)
    {leftMatrix : SetoidMatrix Int} (rightMatrix : SetoidMatrix Int)
    (leftColFits : leftMatrix.colCount = windowSize)
    (leftVanishes : agreeOnWindow leftMatrix (intMatrixZeroSquare windowSize)
      windowSize windowSize) :
    agreeOnWindow (intMatrixMul leftMatrix rightMatrix) (intMatrixZeroSquare windowSize)
      windowSize windowSize := by
  intro rowIndex rowBelow colIndex colBelow
  dsimp only [intMatrixMul, mulMatrix]
  rw [leftColFits]
  exact intDenotesSameIsEq (intCommutativeRingWitness.denotesSameIsTransitive _ _ _
    (sumUpToCongr intCommutativeRingWitness windowSize
      (fun innerIndex innerBelow =>
        intCommutativeRingWitness.denotesSameIsTransitive _ _ _
          (intCommutativeRingWitness.mulRespectsDenotesSame _ _ _ _
            (leftVanishes rowIndex rowBelow innerIndex innerBelow)
            (intCommutativeRingWitness.denotesSameIsReflexive
              (rightMatrix.entry innerIndex colIndex)))
          (zeroMulLeft intCommutativeRingWitness (rightMatrix.entry innerIndex colIndex))))
    (sumUpToZeroTerms intCommutativeRingWitness windowSize))

/-- A window-vanishing right factor kills the product on the window. -/
theorem intMatrixMulVanishingRightFactorOnWindow (windowSize : Nat)
    (leftMatrix : SetoidMatrix Int) {rightMatrix : SetoidMatrix Int}
    (leftColFits : leftMatrix.colCount = windowSize)
    (rightVanishes : agreeOnWindow rightMatrix (intMatrixZeroSquare windowSize)
      windowSize windowSize) :
    agreeOnWindow (intMatrixMul leftMatrix rightMatrix) (intMatrixZeroSquare windowSize)
      windowSize windowSize := by
  intro rowIndex rowBelow colIndex colBelow
  dsimp only [intMatrixMul, mulMatrix]
  rw [leftColFits]
  exact intDenotesSameIsEq (intCommutativeRingWitness.denotesSameIsTransitive _ _ _
    (sumUpToCongr intCommutativeRingWitness windowSize
      (fun innerIndex innerBelow =>
        intCommutativeRingWitness.denotesSameIsTransitive _ _ _
          (intCommutativeRingWitness.mulRespectsDenotesSame _ _ _ _
            (intCommutativeRingWitness.denotesSameIsReflexive
              (leftMatrix.entry rowIndex innerIndex))
            (rightVanishes innerIndex innerBelow colIndex colBelow))
          (mulZeroRight intCommutativeRingWitness (leftMatrix.entry rowIndex innerIndex))))
    (sumUpToZeroTerms intCommutativeRingWitness windowSize))

/-! ## The power ladder -/

/-- The power ladder.  From the two witness window identities `P·Q = d·I` and `Q·(A·P) = d·B` follows,
for every `k`, the scaled power identity

  `d^k · (Q·(A^(k+1)·P))  =  d^(k+1) · B^(k+1)`   (on the `n × n` window).

The scale is carried through the induction (multiply both sides by `Q·(A·P)` and absorb one
`P·Q = d·I` insertion), so no division and no cancellation over ℤ is ever needed. -/
theorem endomorphismWitnessPowerLadder
    (dimension : Nat) (source target changeOfBasis scaledInverse : SetoidMatrix Int)
    (scale : Int)
    (sourceRowFits : source.rowCount = dimension) (sourceColFits : source.colCount = dimension)
    (targetRowFits : target.rowCount = dimension) (targetColFits : target.colCount = dimension)
    (basisColFits : changeOfBasis.colCount = dimension)
    (inverseColFits : scaledInverse.colCount = dimension)
    (inverseWindowHolds : agreeOnWindow (intMatrixMul changeOfBasis scaledInverse)
      (intMatrixScale scale (intMatrixIdentity dimension)) dimension dimension)
    (conjugacyWindowHolds : agreeOnWindow
      (intMatrixMul scaledInverse (intMatrixMul source changeOfBasis))
      (intMatrixScale scale target) dimension dimension) :
    ∀ powerPredecessor : Nat,
      agreeOnWindow
        (intMatrixScale (intPower scale powerPredecessor)
          (intMatrixMul scaledInverse
            (intMatrixMul (endomorphismMatrixPower dimension source (powerPredecessor + 1))
              changeOfBasis)))
        (intMatrixScale (intPower scale (powerPredecessor + 1))
          (endomorphismMatrixPower dimension target (powerPredecessor + 1)))
        dimension dimension := by
  intro powerPredecessor
  induction powerPredecessor with
  | zero =>
      -- A^1 = I·A and B^1 = I·B; strip the identities and the `1` scales.
      have sourceFirstPowerAgrees :
          agreeOnWindow (endomorphismMatrixPower dimension source 1) source
            dimension dimension :=
        intMatrixMulIdentityLeftOnWindow dimension sourceRowFits
      have targetFirstPowerAgrees :
          agreeOnWindow (endomorphismMatrixPower dimension target 1) target
            dimension dimension :=
        intMatrixMulIdentityLeftOnWindow dimension targetRowFits
      have conjugateAgrees :
          agreeOnWindow
            (intMatrixMul scaledInverse
              (intMatrixMul (endomorphismMatrixPower dimension source 1) changeOfBasis))
            (intMatrixScale scale target) dimension dimension :=
        agreeOnWindowTrans
          (intMatrixMulCongrOnWindow dimension inverseColFits inverseColFits
            (agreeOnWindowRefl scaledInverse dimension dimension)
            (intMatrixMulCongrOnWindow dimension sourceColFits sourceColFits
              sourceFirstPowerAgrees (agreeOnWindowRefl changeOfBasis dimension dimension)))
          conjugacyWindowHolds
      have leftStripped :
          agreeOnWindow
            (intMatrixScale (intPower scale 0)
              (intMatrixMul scaledInverse
                (intMatrixMul (endomorphismMatrixPower dimension source 1) changeOfBasis)))
            (intMatrixScale scale target) dimension dimension :=
        agreeOnWindowTrans
          (intMatrixScaleOneOnWindow
            (intMatrixMul scaledInverse
              (intMatrixMul (endomorphismMatrixPower dimension source 1) changeOfBasis))
            dimension dimension)
          conjugateAgrees
      have rightAssembled :
          agreeOnWindow (intMatrixScale scale target)
            (intMatrixScale (intPower scale 1)
              (endomorphismMatrixPower dimension target 1)) dimension dimension := by
        have scaleCollapses : intPower scale 1 = scale := intOneMul scale
        rw [scaleCollapses]
        exact intMatrixScaleCongrOnWindow scale (agreeOnWindowSymm targetFirstPowerAgrees)
      exact agreeOnWindowTrans leftStripped rightAssembled
  | succ powerValue ladderHolds =>
      -- Column-count bookkeeping (all definitional modulo the fits hypotheses).
      have sourcePowerColFits :
          (endomorphismMatrixPower dimension source (powerValue + 1)).colCount = dimension :=
        sourceColFits
      have targetPowerColFits :
          (endomorphismMatrixPower dimension target (powerValue + 1)).colCount = dimension :=
        targetColFits
      -- The multiplier `R := Q·(A·P)`.
      let conjugateProbe := intMatrixMul scaledInverse (intMatrixMul source changeOfBasis)
      -- Multiply both ladder sides on the right by `R`.
      have laddersTimesProbe :
          agreeOnWindow
            (intMatrixMul
              (intMatrixScale (intPower scale powerValue)
                (intMatrixMul scaledInverse
                  (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                    changeOfBasis)))
              conjugateProbe)
            (intMatrixMul
              (intMatrixScale (intPower scale (powerValue + 1))
                (endomorphismMatrixPower dimension target (powerValue + 1)))
              conjugateProbe)
            dimension dimension :=
        intMatrixMulCongrOnWindow dimension basisColFits targetPowerColFits
          ladderHolds (agreeOnWindowRefl conjugateProbe dimension dimension)
      -- The `P·R ≈ d·(A·P)` insertion.
      have basisTimesProbeAgrees :
          agreeOnWindow (intMatrixMul changeOfBasis conjugateProbe)
            (intMatrixScale scale (intMatrixMul source changeOfBasis)) dimension dimension := by
        have reassociated :
            agreeOnWindow (intMatrixMul changeOfBasis conjugateProbe)
              (intMatrixMul (intMatrixMul changeOfBasis scaledInverse)
                (intMatrixMul source changeOfBasis)) dimension dimension :=
          agreeOnWindowSymm
            (intMatrixMulAssocOnWindow changeOfBasis scaledInverse
              (intMatrixMul source changeOfBasis) dimension dimension)
        have inverseInserted :
            agreeOnWindow
              (intMatrixMul (intMatrixMul changeOfBasis scaledInverse)
                (intMatrixMul source changeOfBasis))
              (intMatrixMul (intMatrixScale scale (intMatrixIdentity dimension))
                (intMatrixMul source changeOfBasis)) dimension dimension :=
          intMatrixMulCongrOnWindow dimension inverseColFits rfl
            inverseWindowHolds
            (agreeOnWindowRefl (intMatrixMul source changeOfBasis) dimension dimension)
        have scalePulled :
            agreeOnWindow
              (intMatrixMul (intMatrixScale scale (intMatrixIdentity dimension))
                (intMatrixMul source changeOfBasis))
              (intMatrixScale scale
                (intMatrixMul (intMatrixIdentity dimension)
                  (intMatrixMul source changeOfBasis))) dimension dimension :=
          intMatrixScaleMulLeftOnWindow scale (intMatrixIdentity dimension)
            (intMatrixMul source changeOfBasis) dimension dimension
        have identityAbsorbed :
            agreeOnWindow
              (intMatrixScale scale
                (intMatrixMul (intMatrixIdentity dimension)
                  (intMatrixMul source changeOfBasis)))
              (intMatrixScale scale (intMatrixMul source changeOfBasis)) dimension dimension :=
          intMatrixScaleCongrOnWindow scale
            (intMatrixMulIdentityLeftOnWindow dimension
              (show (intMatrixMul source changeOfBasis).rowCount = dimension from sourceRowFits))
        exact agreeOnWindowTrans reassociated
          (agreeOnWindowTrans inverseInserted (agreeOnWindowTrans scalePulled identityAbsorbed))
      -- Assemble the left side: `(d^k·(Q·(A^(k+1)·P)))·R ≈ d^(k+1)·(Q·(A^(k+2)·P))`.
      have leftSideAssembled :
          agreeOnWindow
            (intMatrixMul
              (intMatrixScale (intPower scale powerValue)
                (intMatrixMul scaledInverse
                  (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                    changeOfBasis)))
              conjugateProbe)
            (intMatrixScale (intPower scale (powerValue + 1))
              (intMatrixMul scaledInverse
                (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 2))
                  changeOfBasis)))
            dimension dimension := by
        have scaleOut :
            agreeOnWindow
              (intMatrixMul
                (intMatrixScale (intPower scale powerValue)
                  (intMatrixMul scaledInverse
                    (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                      changeOfBasis)))
                conjugateProbe)
              (intMatrixScale (intPower scale powerValue)
                (intMatrixMul
                  (intMatrixMul scaledInverse
                    (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                      changeOfBasis))
                  conjugateProbe))
              dimension dimension :=
          intMatrixScaleMulLeftOnWindow (intPower scale powerValue)
            (intMatrixMul scaledInverse
              (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                changeOfBasis))
            conjugateProbe dimension dimension
        have coreAssociatedOnce :
            agreeOnWindow
              (intMatrixMul
                (intMatrixMul scaledInverse
                  (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                    changeOfBasis))
                conjugateProbe)
              (intMatrixMul scaledInverse
                (intMatrixMul
                  (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                    changeOfBasis)
                  conjugateProbe))
              dimension dimension :=
          intMatrixMulAssocOnWindow scaledInverse
            (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
              changeOfBasis)
            conjugateProbe dimension dimension
        have innerAssociated :
            agreeOnWindow
              (intMatrixMul
                (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                  changeOfBasis)
                conjugateProbe)
              (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                (intMatrixMul changeOfBasis conjugateProbe))
              dimension dimension :=
          intMatrixMulAssocOnWindow
            (endomorphismMatrixPower dimension source (powerValue + 1)) changeOfBasis
            conjugateProbe dimension dimension
        have innerInserted :
            agreeOnWindow
              (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                (intMatrixMul changeOfBasis conjugateProbe))
              (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                (intMatrixScale scale (intMatrixMul source changeOfBasis)))
              dimension dimension :=
          intMatrixMulCongrOnWindow dimension sourcePowerColFits sourcePowerColFits
            (agreeOnWindowRefl (endomorphismMatrixPower dimension source (powerValue + 1))
              dimension dimension)
            basisTimesProbeAgrees
        have innerScalePulled :
            agreeOnWindow
              (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                (intMatrixScale scale (intMatrixMul source changeOfBasis)))
              (intMatrixScale scale
                (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                  (intMatrixMul source changeOfBasis)))
              dimension dimension :=
          intMatrixScaleMulRightOnWindow scale
            (endomorphismMatrixPower dimension source (powerValue + 1))
            (intMatrixMul source changeOfBasis) dimension dimension
        have innerReassembled :
            agreeOnWindow
              (intMatrixScale scale
                (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                  (intMatrixMul source changeOfBasis)))
              (intMatrixScale scale
                (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 2))
                  changeOfBasis))
              dimension dimension :=
          intMatrixScaleCongrOnWindow scale
            (agreeOnWindowSymm
              (intMatrixMulAssocOnWindow
                (endomorphismMatrixPower dimension source (powerValue + 1)) source changeOfBasis
                dimension dimension))
        have coreChain :
            agreeOnWindow
              (intMatrixMul
                (intMatrixMul scaledInverse
                  (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 1))
                    changeOfBasis))
                conjugateProbe)
              (intMatrixMul scaledInverse
                (intMatrixScale scale
                  (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 2))
                    changeOfBasis)))
              dimension dimension :=
          agreeOnWindowTrans coreAssociatedOnce
            (intMatrixMulCongrOnWindow dimension inverseColFits inverseColFits
              (agreeOnWindowRefl scaledInverse dimension dimension)
              (agreeOnWindowTrans innerAssociated
                (agreeOnWindowTrans innerInserted
                  (agreeOnWindowTrans innerScalePulled innerReassembled))))
        have outerScalePulled :
            agreeOnWindow
              (intMatrixMul scaledInverse
                (intMatrixScale scale
                  (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 2))
                    changeOfBasis)))
              (intMatrixScale scale
                (intMatrixMul scaledInverse
                  (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 2))
                    changeOfBasis)))
              dimension dimension :=
          intMatrixScaleMulRightOnWindow scale scaledInverse
            (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 2))
              changeOfBasis)
            dimension dimension
        have scalesCollapsed :
            agreeOnWindow
              (intMatrixScale (intPower scale powerValue)
                (intMatrixScale scale
                  (intMatrixMul scaledInverse
                    (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 2))
                      changeOfBasis))))
              (intMatrixScale (intPower scale powerValue * scale)
                (intMatrixMul scaledInverse
                  (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 2))
                    changeOfBasis)))
              dimension dimension :=
          intMatrixScaleCollapseOnWindow (intPower scale powerValue) scale
            (intMatrixMul scaledInverse
              (intMatrixMul (endomorphismMatrixPower dimension source (powerValue + 2))
                changeOfBasis))
            dimension dimension
        exact agreeOnWindowTrans scaleOut
          (agreeOnWindowTrans
            (intMatrixScaleCongrOnWindow (intPower scale powerValue)
              (agreeOnWindowTrans coreChain outerScalePulled))
            scalesCollapsed)
      -- Assemble the right side: `(d^(k+1)·B^(k+1))·R ≈ d^(k+2)·B^(k+2)`.
      have rightSideAssembled :
          agreeOnWindow
            (intMatrixMul
              (intMatrixScale (intPower scale (powerValue + 1))
                (endomorphismMatrixPower dimension target (powerValue + 1)))
              conjugateProbe)
            (intMatrixScale (intPower scale (powerValue + 2))
              (endomorphismMatrixPower dimension target (powerValue + 2)))
            dimension dimension := by
        have scaleOut :
            agreeOnWindow
              (intMatrixMul
                (intMatrixScale (intPower scale (powerValue + 1))
                  (endomorphismMatrixPower dimension target (powerValue + 1)))
                conjugateProbe)
              (intMatrixScale (intPower scale (powerValue + 1))
                (intMatrixMul (endomorphismMatrixPower dimension target (powerValue + 1))
                  conjugateProbe))
              dimension dimension :=
          intMatrixScaleMulLeftOnWindow (intPower scale (powerValue + 1))
            (endomorphismMatrixPower dimension target (powerValue + 1)) conjugateProbe
            dimension dimension
        have probeReplaced :
            agreeOnWindow
              (intMatrixMul (endomorphismMatrixPower dimension target (powerValue + 1))
                conjugateProbe)
              (intMatrixMul (endomorphismMatrixPower dimension target (powerValue + 1))
                (intMatrixScale scale target))
              dimension dimension :=
          intMatrixMulCongrOnWindow dimension targetPowerColFits targetPowerColFits
            (agreeOnWindowRefl (endomorphismMatrixPower dimension target (powerValue + 1))
              dimension dimension)
            conjugacyWindowHolds
        have scalePulled :
            agreeOnWindow
              (intMatrixMul (endomorphismMatrixPower dimension target (powerValue + 1))
                (intMatrixScale scale target))
              (intMatrixScale scale
                (endomorphismMatrixPower dimension target (powerValue + 2)))
              dimension dimension :=
          intMatrixScaleMulRightOnWindow scale
            (endomorphismMatrixPower dimension target (powerValue + 1)) target
            dimension dimension
        have scalesCollapsed :
            agreeOnWindow
              (intMatrixScale (intPower scale (powerValue + 1))
                (intMatrixScale scale
                  (endomorphismMatrixPower dimension target (powerValue + 2))))
              (intMatrixScale (intPower scale (powerValue + 1) * scale)
                (endomorphismMatrixPower dimension target (powerValue + 2)))
              dimension dimension :=
          intMatrixScaleCollapseOnWindow (intPower scale (powerValue + 1)) scale
            (endomorphismMatrixPower dimension target (powerValue + 2)) dimension dimension
        exact agreeOnWindowTrans scaleOut
          (agreeOnWindowTrans
            (intMatrixScaleCongrOnWindow (intPower scale (powerValue + 1))
              (agreeOnWindowTrans probeReplaced scalePulled))
            scalesCollapsed)
      exact agreeOnWindowTrans (agreeOnWindowSymm leftSideAssembled)
        (agreeOnWindowTrans laddersTimesProbe rightSideAssembled)

/-! ## Power vanishing and its transport across a witness -/

/-- The `powerExponent`-th power of `matrix` vanishes on the `dimension × dimension` window.
Decidable at concrete inputs (bounded window over `Int` entries). -/
@[reducible] def endomorphismPowerVanishesOnWindow
    (dimension powerExponent : Nat) (matrix : SetoidMatrix Int) : Prop :=
  agreeOnWindow (endomorphismMatrixPower dimension matrix powerExponent)
    (intMatrixZeroSquare dimension) dimension dimension

/-- Vanishing transports source → target.  If a coherent-dimension witness holds and the source's
`(k+1)`-th power vanishes on the window, so does the target's: the ladder pins
`d^(k+1) · B^(k+1) = d^k · (Q·(A^(k+1)·P)) = 0` entrywise, and the nonzero `d`-power cancels. -/
theorem endomorphismWitnessTransportsPowerVanishing
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
    (powerPredecessor : Nat)
    (sourcePowerVanishes :
      endomorphismPowerVanishesOnWindow dimension (powerPredecessor + 1) source) :
    endomorphismPowerVanishesOnWindow dimension (powerPredecessor + 1) target := by
  have conjugatedVanishes :
      agreeOnWindow
        (intMatrixMul scaledInverse
          (intMatrixMul (endomorphismMatrixPower dimension source (powerPredecessor + 1))
            changeOfBasis))
        (intMatrixZeroSquare dimension) dimension dimension :=
    intMatrixMulVanishingRightFactorOnWindow dimension scaledInverse inverseColFits
      (intMatrixMulVanishingLeftFactorOnWindow dimension changeOfBasis
        (show (endomorphismMatrixPower dimension source (powerPredecessor + 1)).colCount
            = dimension from sourceColFits)
        sourcePowerVanishes)
  have ladderHolds := endomorphismWitnessPowerLadder dimension source target changeOfBasis
    scaledInverse scale sourceRowFits sourceColFits targetRowFits targetColFits basisColFits
    inverseColFits inverseWindowHolds conjugacyWindowHolds powerPredecessor
  intro rowIndex rowBelow colIndex colBelow
  have scaledTargetEntryIsZero :
      intPower scale (powerPredecessor + 1)
          * (endomorphismMatrixPower dimension target (powerPredecessor + 1)).entry
              rowIndex colIndex
        = 0 := by
    have ladderEntry := (ladderHolds rowIndex rowBelow colIndex colBelow).symm
    have conjugatedEntryIsZero :=
      conjugatedVanishes rowIndex rowBelow colIndex colBelow
    exact ladderEntry.trans
      ((congrArg (intPower scale powerPredecessor * ·) conjugatedEntryIsZero).trans
        (intMulZero (intPower scale powerPredecessor)))
  exact intFactorIsZeroOfPowerScaledZero scaleHasMagnitude (powerPredecessor + 1) _
    scaledTargetEntryIsZero

/-- Vanishing reflects target → source.  If a coherent-dimension witness holds and the target's
`(k+1)`-th power vanishes, the ladder first kills `Q·(A^(k+1)·P)` on the window (cancel `d^k`), and
the sandwich `(P·Q)·A^(k+1)·(P·Q) = d²·A^(k+1)` then kills `A^(k+1)` itself (cancel `d` twice). -/
theorem endomorphismWitnessReflectsPowerVanishing
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
    (powerPredecessor : Nat)
    (targetPowerVanishes :
      endomorphismPowerVanishesOnWindow dimension (powerPredecessor + 1) target) :
    endomorphismPowerVanishesOnWindow dimension (powerPredecessor + 1) source := by
  have ladderHolds := endomorphismWitnessPowerLadder dimension source target changeOfBasis
    scaledInverse scale sourceRowFits sourceColFits targetRowFits targetColFits basisColFits
    inverseColFits inverseWindowHolds conjugacyWindowHolds powerPredecessor
  -- Step 1: `Q·(A^(k+1)·P)` vanishes on the window.
  have conjugatedVanishes :
      agreeOnWindow
        (intMatrixMul scaledInverse
          (intMatrixMul (endomorphismMatrixPower dimension source (powerPredecessor + 1))
            changeOfBasis))
        (intMatrixZeroSquare dimension) dimension dimension := by
    intro rowIndex rowBelow colIndex colBelow
    have scaledEntryIsZero :
        intPower scale powerPredecessor
            * (intMatrixMul scaledInverse
                (intMatrixMul (endomorphismMatrixPower dimension source (powerPredecessor + 1))
                  changeOfBasis)).entry rowIndex colIndex
          = 0 := by
      have ladderEntry := ladderHolds rowIndex rowBelow colIndex colBelow
      have targetEntryIsZero := targetPowerVanishes rowIndex rowBelow colIndex colBelow
      exact ladderEntry.trans
        ((congrArg (intPower scale (powerPredecessor + 1) * ·) targetEntryIsZero).trans
          (intMulZero (intPower scale (powerPredecessor + 1))))
    exact intFactorIsZeroOfPowerScaledZero scaleHasMagnitude powerPredecessor _
      scaledEntryIsZero
  -- Step 2: the sandwich `P·((Q·(A^(k+1)·P))·Q) ≈ d²·A^(k+1)` vanishes, so `A^(k+1)` does.
  let sourcePower := endomorphismMatrixPower dimension source (powerPredecessor + 1)
  have sourcePowerRowFits : sourcePower.rowCount = dimension :=
    endomorphismMatrixPowerRowCount dimension source (powerPredecessor + 1)
  have sourcePowerColFits : sourcePower.colCount = dimension := sourceColFits
  have sandwichVanishes :
      agreeOnWindow
        (intMatrixMul changeOfBasis
          (intMatrixMul
            (intMatrixMul scaledInverse (intMatrixMul sourcePower changeOfBasis))
            scaledInverse))
        (intMatrixZeroSquare dimension) dimension dimension :=
    intMatrixMulVanishingRightFactorOnWindow dimension changeOfBasis basisColFits
      (intMatrixMulVanishingLeftFactorOnWindow dimension scaledInverse
        (show (intMatrixMul scaledInverse (intMatrixMul sourcePower changeOfBasis)).colCount
            = dimension from basisColFits)
        conjugatedVanishes)
  have sandwichAlgebra :
      agreeOnWindow
        (intMatrixMul changeOfBasis
          (intMatrixMul
            (intMatrixMul scaledInverse (intMatrixMul sourcePower changeOfBasis))
            scaledInverse))
        (intMatrixScale (scale * scale) sourcePower) dimension dimension := by
    have innerAssociated :
        agreeOnWindow
          (intMatrixMul
            (intMatrixMul scaledInverse (intMatrixMul sourcePower changeOfBasis))
            scaledInverse)
          (intMatrixMul scaledInverse
            (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse))
          dimension dimension :=
      intMatrixMulAssocOnWindow scaledInverse (intMatrixMul sourcePower changeOfBasis)
        scaledInverse dimension dimension
    have outerLifted :
        agreeOnWindow
          (intMatrixMul changeOfBasis
            (intMatrixMul
              (intMatrixMul scaledInverse (intMatrixMul sourcePower changeOfBasis))
              scaledInverse))
          (intMatrixMul changeOfBasis
            (intMatrixMul scaledInverse
              (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse)))
          dimension dimension :=
      intMatrixMulCongrOnWindow dimension basisColFits basisColFits
        (agreeOnWindowRefl changeOfBasis dimension dimension) innerAssociated
    have outerAssociated :
        agreeOnWindow
          (intMatrixMul changeOfBasis
            (intMatrixMul scaledInverse
              (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse)))
          (intMatrixMul (intMatrixMul changeOfBasis scaledInverse)
            (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse))
          dimension dimension :=
      agreeOnWindowSymm
        (intMatrixMulAssocOnWindow changeOfBasis scaledInverse
          (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse)
          dimension dimension)
    have leftInverseInserted :
        agreeOnWindow
          (intMatrixMul (intMatrixMul changeOfBasis scaledInverse)
            (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse))
          (intMatrixMul (intMatrixScale scale (intMatrixIdentity dimension))
            (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse))
          dimension dimension :=
      intMatrixMulCongrOnWindow dimension inverseColFits rfl inverseWindowHolds
        (agreeOnWindowRefl
          (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse)
          dimension dimension)
    have leftScalePulled :
        agreeOnWindow
          (intMatrixMul (intMatrixScale scale (intMatrixIdentity dimension))
            (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse))
          (intMatrixScale scale
            (intMatrixMul (intMatrixIdentity dimension)
              (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse)))
          dimension dimension :=
      intMatrixScaleMulLeftOnWindow scale (intMatrixIdentity dimension)
        (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse)
        dimension dimension
    have leftIdentityAbsorbed :
        agreeOnWindow
          (intMatrixMul (intMatrixIdentity dimension)
            (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse))
          (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse)
          dimension dimension :=
      intMatrixMulIdentityLeftOnWindow dimension
        (show (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse).rowCount
            = dimension from sourcePowerRowFits)
    have coreAssociated :
        agreeOnWindow
          (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse)
          (intMatrixMul sourcePower (intMatrixMul changeOfBasis scaledInverse))
          dimension dimension :=
      intMatrixMulAssocOnWindow sourcePower changeOfBasis scaledInverse dimension dimension
    have rightInverseInserted :
        agreeOnWindow
          (intMatrixMul sourcePower (intMatrixMul changeOfBasis scaledInverse))
          (intMatrixMul sourcePower (intMatrixScale scale (intMatrixIdentity dimension)))
          dimension dimension :=
      intMatrixMulCongrOnWindow dimension sourcePowerColFits sourcePowerColFits
        (agreeOnWindowRefl sourcePower dimension dimension) inverseWindowHolds
    have rightScalePulled :
        agreeOnWindow
          (intMatrixMul sourcePower (intMatrixScale scale (intMatrixIdentity dimension)))
          (intMatrixScale scale (intMatrixMul sourcePower (intMatrixIdentity dimension)))
          dimension dimension :=
      intMatrixScaleMulRightOnWindow scale sourcePower (intMatrixIdentity dimension)
        dimension dimension
    have rightIdentityAbsorbed :
        agreeOnWindow
          (intMatrixScale scale (intMatrixMul sourcePower (intMatrixIdentity dimension)))
          (intMatrixScale scale sourcePower) dimension dimension :=
      intMatrixScaleCongrOnWindow scale
        (intMatrixMulIdentityRightOnWindow dimension sourcePowerColFits)
    have coreChain :
        agreeOnWindow
          (intMatrixMul (intMatrixMul sourcePower changeOfBasis) scaledInverse)
          (intMatrixScale scale sourcePower) dimension dimension :=
      agreeOnWindowTrans coreAssociated
        (agreeOnWindowTrans rightInverseInserted
          (agreeOnWindowTrans rightScalePulled rightIdentityAbsorbed))
    have scalesCollapsed :
        agreeOnWindow
          (intMatrixScale scale (intMatrixScale scale sourcePower))
          (intMatrixScale (scale * scale) sourcePower) dimension dimension :=
      intMatrixScaleCollapseOnWindow scale scale sourcePower dimension dimension
    exact agreeOnWindowTrans outerLifted
      (agreeOnWindowTrans outerAssociated
        (agreeOnWindowTrans leftInverseInserted
          (agreeOnWindowTrans leftScalePulled
            (agreeOnWindowTrans
              (intMatrixScaleCongrOnWindow scale
                (agreeOnWindowTrans leftIdentityAbsorbed coreChain))
              scalesCollapsed))))
  intro rowIndex rowBelow colIndex colBelow
  have doubleScaledEntryIsZero :
      scale * scale * sourcePower.entry rowIndex colIndex = 0 :=
    ((sandwichAlgebra rowIndex rowBelow colIndex colBelow).symm.trans
      (sandwichVanishes rowIndex rowBelow colIndex colBelow))
  have singleScaledEntryIsZero : scale * sourcePower.entry rowIndex colIndex = 0 :=
    intFactorIsZeroOfScaledZero (scale * sourcePower.entry rowIndex colIndex)
      scaleHasMagnitude
      ((intMulAssoc scale scale (sourcePower.entry rowIndex colIndex)).symm.trans
        doubleScaledEntryIsZero)
  exact intFactorIsZeroOfScaledZero (sourcePower.entry rowIndex colIndex) scaleHasMagnitude
    singleScaledEntryIsZero

/-! ## The dimension-junk forgery against the raw checker, and the additive repair -/

/-- A forged witness against the machine-checked dissimilar pair `[[1,0],[0,0]]` vs `[[2,0],[0,0]]`: the
change of basis is `2×3` and the scaled inverse `3×2`, and the phantom third column/row cancels inside
`P·Q` (contributing `2·1 + 0 + 1·(-1) = 1`) while staying invisible to `Q·(A·P)`. -/
def endomorphismDimensionForgeryWitness : EndomorphismSimilarityWitness :=
  { dimension := 2
    source := setoidMatrixOfRows [[1, 0], [0, 0]]
    target := setoidMatrixOfRows [[2, 0], [0, 0]]
    changeOfBasis := setoidMatrixOfRows [[2, 0, 1], [0, 1, 0]]
    scaledInverse := setoidMatrixOfRows [[1, 0], [0, 1], [-1, 0]]
    scale := 1 }

/-- The checker gap, machine-checked: the forgery passes the raw `WitnessesSimilarity` even though its
source/target pair is the `endomorphismDistinctTraceDissimilar` pair.  The raw checker never constrains
the conjugator dimension fields, and the window sums range over the operands' intrinsic `colCount`s. -/
theorem endomorphismDimensionForgeryPassesRawChecker :
    endomorphismDimensionForgeryWitness.WitnessesSimilarity := by decide

/-- The additively-repaired checker: the raw window checks plus the eight dimension-coherence equations
tying every matrix field's shape to the declared `dimension`.  Every shipped witness satisfies the
extra conjuncts by `rfl`; the forgery does not. -/
@[reducible] def EndomorphismSimilarityWitness.WitnessesSimilarityWithCoherentDimensions
    (witness : EndomorphismSimilarityWitness) : Prop :=
  witness.source.rowCount = witness.dimension
  ∧ witness.source.colCount = witness.dimension
  ∧ witness.target.rowCount = witness.dimension
  ∧ witness.target.colCount = witness.dimension
  ∧ witness.changeOfBasis.rowCount = witness.dimension
  ∧ witness.changeOfBasis.colCount = witness.dimension
  ∧ witness.scaledInverse.rowCount = witness.dimension
  ∧ witness.scaledInverse.colCount = witness.dimension
  ∧ witness.WitnessesSimilarity

/-- The forgery is rejected by the coherent-dimension checker (its change of basis is `2×3`). -/
theorem endomorphismDimensionForgeryRejectedWithCoherence :
    ¬ endomorphismDimensionForgeryWitness.WitnessesSimilarityWithCoherentDimensions := by decide

/-- Both shipped similar witnesses pass the strengthened checker — the dimension conjuncts cost nothing
on honest instances. -/
theorem endomorphismShippedWitnessesPassCoherentChecker :
    endomorphismNilpotentConjugacyWitness.WitnessesSimilarityWithCoherentDimensions
      ∧ endomorphismRationalConjugacyWitness.WitnessesSimilarityWithCoherentDimensions := by
  decide

/-! ## The rank-sequence separator (rank-zero boundary) and its refutation theorems -/

/-- The rank-sequence separator at the rank-`0` boundary: at the `powerExponent`-th power, exactly one
of the two matrices vanishes on the window (`rank = 0` vs `> 0`); either orientation counts.  Decidable
at concrete inputs; its dissimilarity force is the proven
`endomorphismRankSequenceSeparationRefutesWitness` below. -/
@[reducible] def EndomorphismDissimilarByRankSequence
    (dimension powerExponent : Nat) (source target : SetoidMatrix Int) : Prop :=
  (endomorphismPowerVanishesOnWindow dimension powerExponent source
      ∧ ¬ endomorphismPowerVanishesOnWindow dimension powerExponent target)
    ∨ (endomorphismPowerVanishesOnWindow dimension powerExponent target
      ∧ ¬ endomorphismPowerVanishesOnWindow dimension powerExponent source)

/-- The separator is symmetric in its two matrices. -/
theorem endomorphismDissimilarByRankSequenceSymm
    {dimension powerExponent : Nat} {source target : SetoidMatrix Int}
    (separated : EndomorphismDissimilarByRankSequence dimension powerExponent source target) :
    EndomorphismDissimilarByRankSequence dimension powerExponent target source :=
  match separated with
  | Or.inl sourceSide => Or.inr sourceSide
  | Or.inr targetSide => Or.inl targetSide

/-- The ∀-witness refutation.  A rank-sequence separation at any positive power refutes every
coherent-dimension witness for the pair: no change of basis, no scaled inverse, no scale.  This is the
machine-proved invariance direction the certificate-level separators lacked. -/
theorem endomorphismRankSequenceSeparationRefutesWitness
    (witness : EndomorphismSimilarityWitness) (powerPredecessor : Nat)
    (separated : EndomorphismDissimilarByRankSequence witness.dimension
      (powerPredecessor + 1) witness.source witness.target) :
    ¬ witness.WitnessesSimilarityWithCoherentDimensions := by
  intro isWitnessed
  obtain ⟨sourceRowFits, sourceColFits, targetRowFits, targetColFits, basisRowFits,
    basisColFits, inverseRowFits, inverseColFits, scaleHasMagnitude, inverseWindowHolds,
    conjugacyWindowHolds⟩ := isWitnessed
  cases separated with
  | inl sourceSide =>
      exact sourceSide.right
        (endomorphismWitnessTransportsPowerVanishing witness.dimension witness.source
          witness.target witness.changeOfBasis witness.scaledInverse witness.scale
          scaleHasMagnitude sourceRowFits sourceColFits targetRowFits targetColFits
          basisColFits inverseColFits inverseWindowHolds conjugacyWindowHolds
          powerPredecessor sourceSide.left)
  | inr targetSide =>
      exact targetSide.right
        (endomorphismWitnessReflectsPowerVanishing witness.dimension witness.source
          witness.target witness.changeOfBasis witness.scaledInverse witness.scale
          scaleHasMagnitude sourceRowFits sourceColFits targetRowFits targetColFits
          basisColFits inverseColFits inverseWindowHolds conjugacyWindowHolds
          powerPredecessor targetSide.left)

/-! ## Decided instances

Three graduated instances, each with a kernel-`decide` separation pin and (for the new pairs) the
∀-quantified no-witness corollaries in BOTH orientations. -/

/-- The subtle pair (zero vs the `2×2` Jordan block), re-decided through the rank-sequence separator at
the first power — continuity with the hub census. -/
theorem endomorphismZeroVersusJordanSeparatedByRankSequence :
    EndomorphismDissimilarByRankSequence 2 1
      (setoidMatrixOfRows [[0, 0], [0, 0]]) (setoidMatrixOfRows [[0, 1], [0, 0]]) := by decide

/-- The `3×3` nilpotent index pair `J2⊕J1` (index 2) vs `J3` (index 3): separated at the SECOND
power (`(J2⊕J1)² = 0`, `J3² ≠ 0`). -/
theorem endomorphismSplitVersusFullJordanSeparatedAtSquare :
    EndomorphismDissimilarByRankSequence 3 2
      (setoidMatrixOfRows [[0, 1, 0], [0, 0, 0], [0, 0, 0]])
      (setoidMatrixOfRows [[0, 1, 0], [0, 0, 1], [0, 0, 0]]) := by decide

/-- The `3×3` pair shares its characteristic polynomial (`x³`, via the closed-form engine): char poly
is blind here, only the power pattern separates. -/
theorem endomorphismSplitVersusFullJordanShareCharPoly :
    endomorphismCharPolyCoefficients 3
        (setoidMatrixOfRows [[0, 1, 0], [0, 0, 0], [0, 0, 0]])
      = endomorphismCharPolyCoefficients 3
          (setoidMatrixOfRows [[0, 1, 0], [0, 0, 1], [0, 0, 0]]) := by decide

/-- No coherent-dimension witness makes `J2⊕J1` similar to `J3` (source → target orientation),
for ANY change of basis, scaled inverse, and scale. -/
theorem endomorphismSplitVersusFullJordanNoWitness :
    ∀ (changeOfBasis scaledInverse : SetoidMatrix Int) (scale : Int),
      ¬ (EndomorphismSimilarityWitness.mk 3
            (setoidMatrixOfRows [[0, 1, 0], [0, 0, 0], [0, 0, 0]])
            (setoidMatrixOfRows [[0, 1, 0], [0, 0, 1], [0, 0, 0]])
            changeOfBasis scaledInverse
            scale).WitnessesSimilarityWithCoherentDimensions :=
  fun changeOfBasis scaledInverse scale =>
    endomorphismRankSequenceSeparationRefutesWitness
      (EndomorphismSimilarityWitness.mk 3
        (setoidMatrixOfRows [[0, 1, 0], [0, 0, 0], [0, 0, 0]])
        (setoidMatrixOfRows [[0, 1, 0], [0, 0, 1], [0, 0, 0]])
        changeOfBasis scaledInverse scale)
      1 endomorphismSplitVersusFullJordanSeparatedAtSquare

/-- The mirrored orientation: no coherent-dimension witness makes `J3` similar to `J2⊕J1`. -/
theorem endomorphismFullVersusSplitJordanNoWitness :
    ∀ (changeOfBasis scaledInverse : SetoidMatrix Int) (scale : Int),
      ¬ (EndomorphismSimilarityWitness.mk 3
            (setoidMatrixOfRows [[0, 1, 0], [0, 0, 1], [0, 0, 0]])
            (setoidMatrixOfRows [[0, 1, 0], [0, 0, 0], [0, 0, 0]])
            changeOfBasis scaledInverse
            scale).WitnessesSimilarityWithCoherentDimensions :=
  fun changeOfBasis scaledInverse scale =>
    endomorphismRankSequenceSeparationRefutesWitness
      (EndomorphismSimilarityWitness.mk 3
        (setoidMatrixOfRows [[0, 1, 0], [0, 0, 1], [0, 0, 0]])
        (setoidMatrixOfRows [[0, 1, 0], [0, 0, 0], [0, 0, 0]])
        changeOfBasis scaledInverse scale)
      1
      (endomorphismDissimilarByRankSequenceSymm
        endomorphismSplitVersusFullJordanSeparatedAtSquare)

/-- The rank-blind `4×4` pair `J2⊕J2` vs `J3⊕J1` (the smallest equal-char-poly, equal-first-rank,
still-dissimilar pair): separated at the second power (`(J2⊕J2)² = 0`, `(J3⊕J1)² ≠ 0`). -/
theorem endomorphismJordanTwoTwoVersusThreeOneSeparatedAtSquare :
    EndomorphismDissimilarByRankSequence 4 2
      (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]])
      (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]) := by decide

/-- No coherent-dimension witness makes `J2⊕J2` similar to `J3⊕J1`. -/
theorem endomorphismJordanTwoTwoVersusThreeOneNoWitness :
    ∀ (changeOfBasis scaledInverse : SetoidMatrix Int) (scale : Int),
      ¬ (EndomorphismSimilarityWitness.mk 4
            (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]])
            (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]])
            changeOfBasis scaledInverse
            scale).WitnessesSimilarityWithCoherentDimensions :=
  fun changeOfBasis scaledInverse scale =>
    endomorphismRankSequenceSeparationRefutesWitness
      (EndomorphismSimilarityWitness.mk 4
        (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]])
        (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]])
        changeOfBasis scaledInverse scale)
      1 endomorphismJordanTwoTwoVersusThreeOneSeparatedAtSquare

/-- The mirrored orientation for the `4×4` pair. -/
theorem endomorphismJordanThreeOneVersusTwoTwoNoWitness :
    ∀ (changeOfBasis scaledInverse : SetoidMatrix Int) (scale : Int),
      ¬ (EndomorphismSimilarityWitness.mk 4
            (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]])
            (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]])
            changeOfBasis scaledInverse
            scale).WitnessesSimilarityWithCoherentDimensions :=
  fun changeOfBasis scaledInverse scale =>
    endomorphismRankSequenceSeparationRefutesWitness
      (EndomorphismSimilarityWitness.mk 4
        (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]])
        (setoidMatrixOfRows [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]])
        changeOfBasis scaledInverse scale)
      1
      (endomorphismDissimilarByRankSequenceSymm
        endomorphismJordanTwoTwoVersusThreeOneSeparatedAtSquare)

end FX1Poly.ComputerAlgebra
