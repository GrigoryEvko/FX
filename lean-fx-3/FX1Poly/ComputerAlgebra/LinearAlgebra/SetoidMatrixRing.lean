import FX1Poly.ComputerAlgebra.LinearAlgebra.SetoidMatrix

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SetoidMatrixRing — matrix multiplication + the ring laws

The multiplicative half of the setoid matrix ring: a structural finite-sum toolkit
(`sumUpTo` + its congruence/linearity/Fubini lemmas), matrix multiplication, and the ring laws that
depend on it — multiplication congruence, associativity, left/right distributivity over addition,
and the (windowed, per-entry) identity laws.

Everything is stated over an arbitrary `CommutativeRingWitness carrier`, so a matrix ring over
ℤ/ℚ/ℝ/ℂ is four instantiations of the same theorems.

## Why per-entry identity laws

`DenoteSame` compares entries at every index, but the identity `mul A I ≈ A` only holds inside the
`rowCount × colCount` window (off-window entries of `A` are junk the identity cannot reproduce).
The associativity and distributivity laws hold at every index, so they are full `DenoteSame`; the
identity laws are honestly stated per-entry with an in-window hypothesis.

## Zero-axiom design

  * `sumUpTo` is structural on its `Nat` bound — no `WellFounded.fix`.
  * Base-ring mirror lemmas (`mulZeroRight`, `oneMulLeft`, …) are derived from the witness's
    right-sided laws plus commutativity, never assumed.
  * The Kronecker-delta pick lemmas case-split on `Nat.decEq` (structural) via the axiom-free
    `if_pos`/`if_neg`, and use only `Init` `Nat` order lemmas.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SetoidMatrixRing.lean`.
-/

namespace FX1Poly.ComputerAlgebra

namespace SetoidMatrix

/-- A plain equality lifts into the base setoid. -/
theorem denotesSameOfEq {carrier : Type} (ring : CommutativeRingWitness carrier)
    {leftValue rightValue : carrier} (areEqual : leftValue = rightValue) :
    ring.denotesSame leftValue rightValue :=
  areEqual ▸ ring.denotesSameIsReflexive leftValue

/-! ## Derived base-ring lemmas (mirrors of the right-sided witness laws) -/

/-- Left additive identity: `0 + value ≈ value`. -/
theorem addZeroLeft {carrier : Type} (ring : CommutativeRingWitness carrier) (value : carrier) :
    ring.denotesSame (ring.add ring.zero value) value :=
  ring.denotesSameIsTransitive _ _ _ (ring.addIsCommutative ring.zero value)
    (ring.zeroIsRightAdditiveIdentity value)

/-- A self-idempotent sum is the zero: `x + x ≈ x` forces `x ≈ 0`. -/
theorem selfAddIdempotentImpliesZero {carrier : Type} (ring : CommutativeRingWitness carrier)
    (value : carrier) (isIdempotent : ring.denotesSame (ring.add value value) value) :
    ring.denotesSame value ring.zero :=
  ring.denotesSameIsTransitive _ _ _
    (ring.denotesSameIsTransitive _ _ _
      (ring.denotesSameIsTransitive _ _ _
        (ring.denotesSameIsSymmetric _ _ (ring.zeroIsRightAdditiveIdentity value))
        (ring.addRespectsDenotesSame _ _ _ _ (ring.denotesSameIsReflexive value)
          (ring.denotesSameIsSymmetric _ _ (ring.negIsRightAdditiveInverse value))))
      (ring.denotesSameIsTransitive _ _ _
        (ring.denotesSameIsSymmetric _ _ (ring.addIsAssociative value value (ring.neg value)))
        (ring.addRespectsDenotesSame _ _ _ _ isIdempotent (ring.denotesSameIsReflexive _))))
    (ring.negIsRightAdditiveInverse value)

/-- Right absorption: `value * 0 ≈ 0`. -/
theorem mulZeroRight {carrier : Type} (ring : CommutativeRingWitness carrier) (value : carrier) :
    ring.denotesSame (ring.mul value ring.zero) ring.zero :=
  selfAddIdempotentImpliesZero ring (ring.mul value ring.zero)
    (ring.denotesSameIsTransitive _ _ _
      (ring.denotesSameIsSymmetric _ _
        (ring.mulDistributesOverAdd value ring.zero ring.zero))
      (ring.mulRespectsDenotesSame _ _ _ _ (ring.denotesSameIsReflexive value)
        (ring.zeroIsRightAdditiveIdentity ring.zero)))

/-- Left absorption: `0 * value ≈ 0`. -/
theorem zeroMulLeft {carrier : Type} (ring : CommutativeRingWitness carrier) (value : carrier) :
    ring.denotesSame (ring.mul ring.zero value) ring.zero :=
  ring.denotesSameIsTransitive _ _ _ (ring.mulIsCommutative ring.zero value)
    (mulZeroRight ring value)

/-- Left multiplicative identity: `1 * value ≈ value`. -/
theorem oneMulLeft {carrier : Type} (ring : CommutativeRingWitness carrier) (value : carrier) :
    ring.denotesSame (ring.mul ring.one value) value :=
  ring.denotesSameIsTransitive _ _ _ (ring.mulIsCommutative ring.one value)
    (ring.oneIsRightMultiplicativeIdentity value)

/-- Right distributivity: `(a + b) * c ≈ a*c + b*c`, from left distributivity via commutativity. -/
theorem mulRightDistributesOverAdd {carrier : Type} (ring : CommutativeRingWitness carrier)
    (leftSummand rightSummand factor : carrier) :
    ring.denotesSame (ring.mul (ring.add leftSummand rightSummand) factor)
      (ring.add (ring.mul leftSummand factor) (ring.mul rightSummand factor)) :=
  ring.denotesSameIsTransitive _ _ _ (ring.mulIsCommutative (ring.add leftSummand rightSummand) factor)
    (ring.denotesSameIsTransitive _ _ _
      (ring.mulDistributesOverAdd factor leftSummand rightSummand)
      (ring.addRespectsDenotesSame _ _ _ _
        (ring.mulIsCommutative factor leftSummand)
        (ring.mulIsCommutative factor rightSummand)))

/-- Commuted Kronecker condition on the one/zero entries. -/
theorem iteOneZeroCondSymm {carrier : Type} (ring : CommutativeRingWitness carrier)
    (leftIndex rightIndex : Nat) :
    (if leftIndex = rightIndex then ring.one else ring.zero)
      = (if rightIndex = leftIndex then ring.one else ring.zero) :=
  match Nat.decEq leftIndex rightIndex with
  | isTrue areEqual => by rw [if_pos areEqual, if_pos (Eq.symm areEqual)]
  | isFalse areApart => by
      rw [if_neg areApart, if_neg (fun swapped => areApart (Eq.symm swapped))]

/-! ## The structural finite-sum toolkit -/

/-- `sumUpTo bound termFn = termFn 0 + termFn 1 + ... + termFn (bound-1)`, folded left with the
running total on the left of each `add`.  Structural on `bound`. -/
def sumUpTo {carrier : Type} (ring : CommutativeRingWitness carrier) :
    Nat → (Nat → carrier) → carrier
  | 0, _ => ring.zero
  | Nat.succ bound, termFn => ring.add (sumUpTo ring bound termFn) (termFn bound)

/-- Equal bounds give setoid-equal sums of the same summand family. -/
theorem sumUpToBoundCongr {carrier : Type} (ring : CommutativeRingWitness carrier)
    {leftBound rightBound : Nat} (boundsAgree : leftBound = rightBound) (termFn : Nat → carrier) :
    ring.denotesSame (sumUpTo ring leftBound termFn) (sumUpTo ring rightBound termFn) :=
  match rightBound, boundsAgree with
  | _, rfl => ring.denotesSameIsReflexive (sumUpTo ring leftBound termFn)

/-- A pointwise-agreeing summand family yields a setoid-equal sum. -/
theorem sumUpToCongr {carrier : Type} (ring : CommutativeRingWitness carrier)
    (bound : Nat) {leftTermFn rightTermFn : Nat → carrier}
    (termsAgree : ∀ index : Nat, index < bound →
      ring.denotesSame (leftTermFn index) (rightTermFn index)) :
    ring.denotesSame (sumUpTo ring bound leftTermFn) (sumUpTo ring bound rightTermFn) :=
  match bound with
  | 0 => ring.denotesSameIsReflexive ring.zero
  | Nat.succ predecessor =>
      ring.addRespectsDenotesSame _ _ _ _
        (sumUpToCongr ring predecessor
          (fun index isBelow => termsAgree index (Nat.lt_succ_of_lt isBelow)))
        (termsAgree predecessor (Nat.lt_succ_self predecessor))

/-- A sum of zeros is zero. -/
theorem sumUpToZeroTerms {carrier : Type} (ring : CommutativeRingWitness carrier) (bound : Nat) :
    ring.denotesSame (sumUpTo ring bound (fun _ => ring.zero)) ring.zero :=
  match bound with
  | 0 => ring.denotesSameIsReflexive ring.zero
  | Nat.succ predecessor =>
      ring.denotesSameIsTransitive _ _ _
        (ring.zeroIsRightAdditiveIdentity (sumUpTo ring predecessor (fun _ => ring.zero)))
        (sumUpToZeroTerms ring predecessor)

/-- Rearrangement `(a + b) + (c + d) ≈ (a + c) + (b + d)` in the base abelian group. -/
theorem addFourRearrangeMiddle {carrier : Type} (ring : CommutativeRingWitness carrier)
    (firstValue secondValue thirdValue fourthValue : carrier) :
    ring.denotesSame (ring.add (ring.add firstValue secondValue) (ring.add thirdValue fourthValue))
      (ring.add (ring.add firstValue thirdValue) (ring.add secondValue fourthValue)) :=
  ring.denotesSameIsTransitive _ _ _
    (ring.addIsAssociative firstValue secondValue (ring.add thirdValue fourthValue))
    (ring.denotesSameIsTransitive _ _ _
      (ring.addRespectsDenotesSame _ _ _ _ (ring.denotesSameIsReflexive firstValue)
        (ring.denotesSameIsTransitive _ _ _
          (ring.denotesSameIsSymmetric _ _
            (ring.addIsAssociative secondValue thirdValue fourthValue))
          (ring.denotesSameIsTransitive _ _ _
            (ring.addRespectsDenotesSame _ _ _ _
              (ring.addIsCommutative secondValue thirdValue)
              (ring.denotesSameIsReflexive fourthValue))
            (ring.addIsAssociative thirdValue secondValue fourthValue))))
      (ring.denotesSameIsSymmetric _ _
        (ring.addIsAssociative firstValue thirdValue (ring.add secondValue fourthValue))))

/-- Sums add termwise: `sum (f + g) ≈ sum f + sum g`. -/
theorem sumUpToAdd {carrier : Type} (ring : CommutativeRingWitness carrier) (bound : Nat)
    (leftTermFn rightTermFn : Nat → carrier) :
    ring.denotesSame
      (sumUpTo ring bound (fun index => ring.add (leftTermFn index) (rightTermFn index)))
      (ring.add (sumUpTo ring bound leftTermFn) (sumUpTo ring bound rightTermFn)) :=
  match bound with
  | 0 => ring.denotesSameIsSymmetric _ _ (ring.zeroIsRightAdditiveIdentity ring.zero)
  | Nat.succ predecessor =>
      ring.denotesSameIsTransitive _ _ _
        (ring.addRespectsDenotesSame _ _ _ _
          (sumUpToAdd ring predecessor leftTermFn rightTermFn)
          (ring.denotesSameIsReflexive
            (ring.add (leftTermFn predecessor) (rightTermFn predecessor))))
        (addFourRearrangeMiddle ring (sumUpTo ring predecessor leftTermFn)
          (sumUpTo ring predecessor rightTermFn) (leftTermFn predecessor)
          (rightTermFn predecessor))

/-- Right-scalar pulls out of a sum: `sum (fun k => f k * c) ≈ (sum f) * c`. -/
theorem sumUpToMulRight {carrier : Type} (ring : CommutativeRingWitness carrier) (bound : Nat)
    (termFn : Nat → carrier) (factor : carrier) :
    ring.denotesSame (sumUpTo ring bound (fun index => ring.mul (termFn index) factor))
      (ring.mul (sumUpTo ring bound termFn) factor) :=
  match bound with
  | 0 => ring.denotesSameIsSymmetric _ _ (zeroMulLeft ring factor)
  | Nat.succ predecessor =>
      ring.denotesSameIsTransitive _ _ _
        (ring.addRespectsDenotesSame _ _ _ _
          (sumUpToMulRight ring predecessor termFn factor)
          (ring.denotesSameIsReflexive (ring.mul (termFn predecessor) factor)))
        (ring.denotesSameIsSymmetric _ _
          (mulRightDistributesOverAdd ring (sumUpTo ring predecessor termFn)
            (termFn predecessor) factor))

/-- Left-scalar pulls out of a sum: `sum (fun k => c * f k) ≈ c * (sum f)`. -/
theorem sumUpToMulLeft {carrier : Type} (ring : CommutativeRingWitness carrier) (bound : Nat)
    (factor : carrier) (termFn : Nat → carrier) :
    ring.denotesSame (sumUpTo ring bound (fun index => ring.mul factor (termFn index)))
      (ring.mul factor (sumUpTo ring bound termFn)) :=
  match bound with
  | 0 => ring.denotesSameIsSymmetric _ _ (mulZeroRight ring factor)
  | Nat.succ predecessor =>
      ring.denotesSameIsTransitive _ _ _
        (ring.addRespectsDenotesSame _ _ _ _
          (sumUpToMulLeft ring predecessor factor termFn)
          (ring.denotesSameIsReflexive (ring.mul factor (termFn predecessor))))
        (ring.denotesSameIsSymmetric _ _
          (ring.mulDistributesOverAdd factor (sumUpTo ring predecessor termFn)
            (termFn predecessor)))

/-- Fubini for finite sums: the order of two nested sums may be swapped. -/
theorem sumUpToSwap {carrier : Type} (ring : CommutativeRingWitness carrier)
    (outerBound innerBound : Nat) (termFn : Nat → Nat → carrier) :
    ring.denotesSame
      (sumUpTo ring outerBound (fun outerIndex =>
        sumUpTo ring innerBound (fun innerIndex => termFn outerIndex innerIndex)))
      (sumUpTo ring innerBound (fun innerIndex =>
        sumUpTo ring outerBound (fun outerIndex => termFn outerIndex innerIndex))) :=
  match outerBound with
  | 0 =>
      ring.denotesSameIsSymmetric _ _
        (sumUpToZeroTerms ring innerBound)
  | Nat.succ predecessor =>
      ring.denotesSameIsTransitive _ _ _
        (ring.addRespectsDenotesSame _ _ _ _
          (sumUpToSwap ring predecessor innerBound termFn)
          (ring.denotesSameIsReflexive
            (sumUpTo ring innerBound (fun innerIndex => termFn predecessor innerIndex))))
        (ring.denotesSameIsSymmetric _ _
          (sumUpToAdd ring innerBound
            (fun innerIndex =>
              sumUpTo ring predecessor (fun outerIndex => termFn outerIndex innerIndex))
            (fun innerIndex => termFn predecessor innerIndex)))

/-- The Kronecker-delta right-vanishing lemma: below the target every term is absorbed. -/
theorem sumUpToDeltaRightVanishes {carrier : Type} (ring : CommutativeRingWitness carrier)
    (bound : Nat) (termFn : Nat → carrier) (target : Nat) (isBelowTarget : bound ≤ target) :
    ring.denotesSame
      (sumUpTo ring bound
        (fun index => ring.mul (termFn index)
          (if index = target then ring.one else ring.zero)))
      ring.zero :=
  match bound with
  | 0 => ring.denotesSameIsReflexive ring.zero
  | Nat.succ predecessor =>
      have predecessorBelow : predecessor < target := isBelowTarget
      have predecessorApart : predecessor ≠ target := Nat.ne_of_lt predecessorBelow
      ring.denotesSameIsTransitive _ _ _
        (ring.addRespectsDenotesSame _ _ _ _
          (sumUpToDeltaRightVanishes ring predecessor termFn target
            (Nat.le_of_succ_le isBelowTarget))
          (ring.denotesSameIsTransitive _ _ _
            (ring.mulRespectsDenotesSame _ _ _ _
              (ring.denotesSameIsReflexive (termFn predecessor))
              (by rw [if_neg predecessorApart]; exact ring.denotesSameIsReflexive ring.zero))
            (mulZeroRight ring (termFn predecessor))))
        (ring.zeroIsRightAdditiveIdentity ring.zero)

/-- The Kronecker-delta right-pick lemma: `sum (fun k => f k * [k = j]) ≈ f j` for `j` in range. -/
theorem sumUpToDeltaRightPicks {carrier : Type} (ring : CommutativeRingWitness carrier)
    (bound : Nat) (termFn : Nat → carrier) (target : Nat) (isInRange : target < bound) :
    ring.denotesSame
      (sumUpTo ring bound
        (fun index => ring.mul (termFn index)
          (if index = target then ring.one else ring.zero)))
      (termFn target) :=
  match bound with
  | 0 => absurd isInRange (Nat.not_lt_zero target)
  | Nat.succ predecessor =>
      match Nat.decEq target predecessor with
      | isTrue targetIsLast =>
          ring.denotesSameIsTransitive _ _ _
            (ring.addRespectsDenotesSame _ _ _ _
              (sumUpToDeltaRightVanishes ring predecessor termFn target
                (Nat.le_of_eq (Eq.symm targetIsLast)))
              (ring.denotesSameIsTransitive _ _ _
                (ring.mulRespectsDenotesSame _ _ _ _
                  (ring.denotesSameIsReflexive (termFn predecessor))
                  (by rw [if_pos (Eq.symm targetIsLast)]
                      exact ring.denotesSameIsReflexive ring.one))
                (ring.oneIsRightMultiplicativeIdentity (termFn predecessor))))
            (ring.denotesSameIsTransitive _ _ _
              (addZeroLeft ring (termFn predecessor))
              (by rw [targetIsLast]; exact ring.denotesSameIsReflexive (termFn predecessor)))
      | isFalse targetNotLast =>
          have targetBelow : target < predecessor :=
            Nat.lt_of_le_of_ne (Nat.le_of_lt_succ isInRange) targetNotLast
          ring.denotesSameIsTransitive _ _ _
            (ring.addRespectsDenotesSame _ _ _ _
              (sumUpToDeltaRightPicks ring predecessor termFn target targetBelow)
              (ring.denotesSameIsTransitive _ _ _
                (ring.mulRespectsDenotesSame _ _ _ _
                  (ring.denotesSameIsReflexive (termFn predecessor))
                  (by rw [if_neg (fun isEqual => targetNotLast (Eq.symm isEqual))]
                      exact ring.denotesSameIsReflexive ring.zero))
                (mulZeroRight ring (termFn predecessor))))
            (ring.zeroIsRightAdditiveIdentity (termFn target))

/-! ## Matrix multiplication -/

/-- Matrix multiplication: `(A * B)[i][j] = Σ_k A[i][k] * B[k][j]`, summed over `A.colCount`. -/
def mulMatrix {carrier : Type} (ring : CommutativeRingWitness carrier)
    (leftMatrix rightMatrix : SetoidMatrix carrier) : SetoidMatrix carrier :=
  { rowCount := leftMatrix.rowCount, colCount := rightMatrix.colCount,
    entry := fun rowIndex colIndex =>
      sumUpTo ring leftMatrix.colCount
        (fun innerIndex =>
          ring.mul (leftMatrix.entry rowIndex innerIndex) (rightMatrix.entry innerIndex colIndex)) }

/-- Multiplication respects the setoid on both arguments. -/
theorem mulMatrixRespectsDenoteSame {carrier : Type} (ring : CommutativeRingWitness carrier)
    {leftMatrix newLeftMatrix rightMatrix newRightMatrix : SetoidMatrix carrier}
    (leftAgrees : DenoteSame ring leftMatrix newLeftMatrix)
    (rightAgrees : DenoteSame ring rightMatrix newRightMatrix) :
    DenoteSame ring (mulMatrix ring leftMatrix rightMatrix)
      (mulMatrix ring newLeftMatrix newRightMatrix) :=
  { sameRowCount := leftAgrees.sameRowCount
    sameColCount := rightAgrees.sameColCount
    entriesAgree := fun rowIndex colIndex => by
      dsimp only [mulMatrix]
      rw [← leftAgrees.sameColCount]
      exact sumUpToCongr ring leftMatrix.colCount
        (fun innerIndex _ =>
          ring.mulRespectsDenotesSame _ _ _ _
            (leftAgrees.entriesAgree rowIndex innerIndex)
            (rightAgrees.entriesAgree innerIndex colIndex)) }

/-- Matrix multiplication is associative. -/
theorem mulMatrixAssoc {carrier : Type} (ring : CommutativeRingWitness carrier)
    (firstMatrix secondMatrix thirdMatrix : SetoidMatrix carrier) :
    DenoteSame ring
      (mulMatrix ring (mulMatrix ring firstMatrix secondMatrix) thirdMatrix)
      (mulMatrix ring firstMatrix (mulMatrix ring secondMatrix thirdMatrix)) :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      ring.denotesSameIsTransitive _ _ _
        (sumUpToCongr ring secondMatrix.colCount
          (fun middleIndex _ =>
            ring.denotesSameIsSymmetric _ _
              (sumUpToMulRight ring firstMatrix.colCount
                (fun innerIndex =>
                  ring.mul (firstMatrix.entry rowIndex innerIndex)
                    (secondMatrix.entry innerIndex middleIndex))
                (thirdMatrix.entry middleIndex colIndex))))
        (ring.denotesSameIsTransitive _ _ _
          (sumUpToSwap ring secondMatrix.colCount firstMatrix.colCount
            (fun middleIndex innerIndex =>
              ring.mul
                (ring.mul (firstMatrix.entry rowIndex innerIndex)
                  (secondMatrix.entry innerIndex middleIndex))
                (thirdMatrix.entry middleIndex colIndex)))
          (ring.denotesSameIsTransitive _ _ _
            (sumUpToCongr ring firstMatrix.colCount
              (fun innerIndex _ =>
                sumUpToCongr ring secondMatrix.colCount
                  (fun middleIndex _ =>
                    ring.mulIsAssociative (firstMatrix.entry rowIndex innerIndex)
                      (secondMatrix.entry innerIndex middleIndex)
                      (thirdMatrix.entry middleIndex colIndex))))
            (sumUpToCongr ring firstMatrix.colCount
              (fun innerIndex _ =>
                sumUpToMulLeft ring secondMatrix.colCount
                  (firstMatrix.entry rowIndex innerIndex)
                  (fun middleIndex =>
                    ring.mul (secondMatrix.entry innerIndex middleIndex)
                      (thirdMatrix.entry middleIndex colIndex)))))) }

/-- Left distributivity: `A * (B + C) ≈ A*B + A*C`. -/
theorem mulMatrixLeftDistrib {carrier : Type} (ring : CommutativeRingWitness carrier)
    (firstMatrix secondMatrix thirdMatrix : SetoidMatrix carrier) :
    DenoteSame ring (mulMatrix ring firstMatrix (addMatrix ring secondMatrix thirdMatrix))
      (addMatrix ring (mulMatrix ring firstMatrix secondMatrix)
        (mulMatrix ring firstMatrix thirdMatrix)) :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      ring.denotesSameIsTransitive _ _ _
        (sumUpToCongr ring firstMatrix.colCount
          (fun innerIndex _ =>
            ring.mulDistributesOverAdd (firstMatrix.entry rowIndex innerIndex)
              (secondMatrix.entry innerIndex colIndex)
              (thirdMatrix.entry innerIndex colIndex)))
        (sumUpToAdd ring firstMatrix.colCount
          (fun innerIndex =>
            ring.mul (firstMatrix.entry rowIndex innerIndex)
              (secondMatrix.entry innerIndex colIndex))
          (fun innerIndex =>
            ring.mul (firstMatrix.entry rowIndex innerIndex)
              (thirdMatrix.entry innerIndex colIndex))) }

/-- Right distributivity: `(A + B) * C ≈ A*C + B*C` (needs `A`, `B` to share a column count). -/
theorem mulMatrixRightDistrib {carrier : Type} (ring : CommutativeRingWitness carrier)
    (firstMatrix secondMatrix thirdMatrix : SetoidMatrix carrier)
    (colMatch : firstMatrix.colCount = secondMatrix.colCount) :
    DenoteSame ring (mulMatrix ring (addMatrix ring firstMatrix secondMatrix) thirdMatrix)
      (addMatrix ring (mulMatrix ring firstMatrix thirdMatrix)
        (mulMatrix ring secondMatrix thirdMatrix)) :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      ring.denotesSameIsTransitive _ _ _
        (sumUpToCongr ring firstMatrix.colCount
          (fun innerIndex _ =>
            mulRightDistributesOverAdd ring (firstMatrix.entry rowIndex innerIndex)
              (secondMatrix.entry rowIndex innerIndex)
              (thirdMatrix.entry innerIndex colIndex)))
        (ring.denotesSameIsTransitive _ _ _
          (sumUpToAdd ring firstMatrix.colCount
            (fun innerIndex =>
              ring.mul (firstMatrix.entry rowIndex innerIndex)
                (thirdMatrix.entry innerIndex colIndex))
            (fun innerIndex =>
              ring.mul (secondMatrix.entry rowIndex innerIndex)
                (thirdMatrix.entry innerIndex colIndex)))
          (ring.addRespectsDenotesSame _ _ _ _
            (ring.denotesSameIsReflexive
              (sumUpTo ring firstMatrix.colCount
                (fun innerIndex =>
                  ring.mul (firstMatrix.entry rowIndex innerIndex)
                    (thirdMatrix.entry innerIndex colIndex))))
            (sumUpToBoundCongr ring colMatch
              (fun innerIndex =>
                ring.mul (secondMatrix.entry rowIndex innerIndex)
                  (thirdMatrix.entry innerIndex colIndex))))) }

/-! ## The (windowed) multiplicative identity laws -/

/-- Right identity, per entry: inside the window `(A * I)[i][j] ≈ A[i][j]`. -/
theorem mulMatrixIdentityRightEntry {carrier : Type} (ring : CommutativeRingWitness carrier)
    (matrix : SetoidMatrix carrier) (rowIndex colIndex : Nat)
    (colInRange : colIndex < matrix.colCount) :
    ring.denotesSame
      ((mulMatrix ring matrix (identityMatrix ring matrix.colCount)).entry rowIndex colIndex)
      (matrix.entry rowIndex colIndex) :=
  sumUpToDeltaRightPicks ring matrix.colCount
    (fun innerIndex => matrix.entry rowIndex innerIndex) colIndex colInRange

/-- Left identity, per entry: inside the window `(I * A)[i][j] ≈ A[i][j]`. -/
theorem mulMatrixIdentityLeftEntry {carrier : Type} (ring : CommutativeRingWitness carrier)
    (matrix : SetoidMatrix carrier) (rowIndex colIndex : Nat)
    (rowInRange : rowIndex < matrix.rowCount) :
    ring.denotesSame
      ((mulMatrix ring (identityMatrix ring matrix.rowCount) matrix).entry rowIndex colIndex)
      (matrix.entry rowIndex colIndex) :=
  ring.denotesSameIsTransitive _ _ _
    (sumUpToCongr ring matrix.rowCount
      (fun innerIndex _ =>
        ring.denotesSameIsTransitive _ _ _
          (ring.mulRespectsDenotesSame _ _ _ _
            (denotesSameOfEq ring (iteOneZeroCondSymm ring rowIndex innerIndex))
            (ring.denotesSameIsReflexive (matrix.entry innerIndex colIndex)))
          (ring.mulIsCommutative
            (if innerIndex = rowIndex then ring.one else ring.zero)
            (matrix.entry innerIndex colIndex))))
    (sumUpToDeltaRightPicks ring matrix.rowCount
      (fun innerIndex => matrix.entry innerIndex colIndex) rowIndex rowInRange)

end SetoidMatrix

end FX1Poly.ComputerAlgebra
