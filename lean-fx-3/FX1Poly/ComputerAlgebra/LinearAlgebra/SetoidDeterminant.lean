import FX1Poly.ComputerAlgebra.LinearAlgebra.SetoidMatrixRing

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SetoidDeterminant — the exact cofactor determinant

The Laplace / cofactor determinant of a leading `size × size` block, defined by structural recursion
on `size` (first-row expansion) over an arbitrary `CommutativeRingWitness carrier`.  Because it uses
only the ring operations — never division — it is EXACT and, instantiated at ℤ, integer-stable by
construction (the entries never leave the base ring).

This is the specificational, correctness-carrying determinant: its value is a genuine ring element
and it satisfies the setoid congruence, the small base cases, and `det I = 1`.  The fraction-free
Bareiss recurrence (which computes the same value in polynomial time but only divides exactly under
Sylvester's identity) is the separate computational track.

## Zero-axiom design

  * `cofactorDet` and `signAlternating` recurse structurally on the `Nat` size — no `WellFounded.fix`.
  * `minorFirstRow` uses `if colIndex < removedColumn` on `Nat.decLt` (structural); the guard
    `colIndex < 0` reduces to the else branch definitionally via `Nat.ble (_ + 1) 0 = false`.
  * The identity-determinant proof reuses the Kronecker-delta pick lemma to isolate the surviving
    `j = 0` term; every case split is on `Nat.decEq`, discharged by axiom-free `if_pos`/`if_neg`.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SetoidDeterminant.lean`.
-/

namespace FX1Poly.ComputerAlgebra

namespace SetoidMatrix

/-! ## Determinant-specific base-ring helpers -/

/-- Swap the last two factors: `(a * d) * c ≈ (a * c) * d`. -/
theorem mulSwapLastTwo {carrier : Type} (ring : CommutativeRingWitness carrier)
    (firstFactor secondFactor thirdFactor : carrier) :
    ring.denotesSame (ring.mul (ring.mul firstFactor secondFactor) thirdFactor)
      (ring.mul (ring.mul firstFactor thirdFactor) secondFactor) :=
  ring.denotesSameIsTransitive _ _ _
    (ring.mulIsAssociative firstFactor secondFactor thirdFactor)
    (ring.denotesSameIsTransitive _ _ _
      (ring.mulRespectsDenotesSame _ _ _ _ (ring.denotesSameIsReflexive firstFactor)
        (ring.mulIsCommutative secondFactor thirdFactor))
      (ring.denotesSameIsSymmetric _ _
        (ring.mulIsAssociative firstFactor thirdFactor secondFactor)))

/-- The one/zero Kronecker entries collapse a matched successor condition. -/
theorem iteSuccCondCollapse {carrier : Type} (ring : CommutativeRingWitness carrier)
    (leftIndex rightIndex : Nat) :
    (if leftIndex + 1 = rightIndex + 1 then ring.one else ring.zero)
      = (if leftIndex = rightIndex then ring.one else ring.zero) :=
  match Nat.decEq leftIndex rightIndex with
  | isTrue areEqual => by rw [if_pos (congrArg Nat.succ areEqual), if_pos areEqual]
  | isFalse areApart => by
      rw [if_neg (fun succEqual => areApart (Nat.succ.inj succEqual)), if_neg areApart]

/-! ## The minor, the alternating sign, and the determinant -/

/-- Delete row `0` and column `removedColumn`, sliding the later columns down by one. -/
def minorFirstRow {carrier : Type} (matrix : SetoidMatrix carrier)
    (removedColumn : Nat) : SetoidMatrix carrier :=
  { rowCount := matrix.rowCount - 1, colCount := matrix.colCount - 1,
    entry := fun rowIndex colIndex =>
      matrix.entry (rowIndex + 1)
        (if colIndex < removedColumn then colIndex else colIndex + 1) }

/-- The alternating sign `(-1)^exponent`, structural on the exponent. -/
def signAlternating {carrier : Type} (ring : CommutativeRingWitness carrier) : Nat → carrier
  | 0 => ring.one
  | Nat.succ predecessor => ring.neg (signAlternating ring predecessor)

/-- The cofactor determinant of the leading `size × size` block, by first-row Laplace expansion. -/
def cofactorDet {carrier : Type} (ring : CommutativeRingWitness carrier) :
    Nat → SetoidMatrix carrier → carrier
  | 0, _ => ring.one
  | Nat.succ predecessor, matrix =>
      sumUpTo ring (Nat.succ predecessor)
        (fun colIndex =>
          ring.mul
            (ring.mul (signAlternating ring colIndex) (matrix.entry 0 colIndex))
            (cofactorDet ring predecessor (minorFirstRow matrix colIndex)))

/-! ## Congruence and base cases -/

/-- The minor respects the setoid. -/
theorem minorFirstRowRespects {carrier : Type} (ring : CommutativeRingWitness carrier)
    {leftMatrix rightMatrix : SetoidMatrix carrier}
    (areSame : DenoteSame ring leftMatrix rightMatrix) (removedColumn : Nat) :
    DenoteSame ring (minorFirstRow leftMatrix removedColumn)
      (minorFirstRow rightMatrix removedColumn) :=
  { sameRowCount := congrArg (fun count => count - 1) areSame.sameRowCount
    sameColCount := congrArg (fun count => count - 1) areSame.sameColCount
    entriesAgree := fun rowIndex colIndex =>
      areSame.entriesAgree (rowIndex + 1)
        (if colIndex < removedColumn then colIndex else colIndex + 1) }

/-- The determinant respects the setoid. -/
theorem cofactorDetCongr {carrier : Type} (ring : CommutativeRingWitness carrier) (size : Nat)
    {leftMatrix rightMatrix : SetoidMatrix carrier}
    (areSame : DenoteSame ring leftMatrix rightMatrix) :
    ring.denotesSame (cofactorDet ring size leftMatrix) (cofactorDet ring size rightMatrix) :=
  match size with
  | 0 => ring.denotesSameIsReflexive ring.one
  | Nat.succ predecessor =>
      sumUpToCongr ring (Nat.succ predecessor)
        (fun colIndex _ =>
          ring.mulRespectsDenotesSame _ _ _ _
            (ring.mulRespectsDenotesSame _ _ _ _
              (ring.denotesSameIsReflexive (signAlternating ring colIndex))
              (areSame.entriesAgree 0 colIndex))
            (cofactorDetCongr ring predecessor (minorFirstRowRespects ring areSame colIndex)))

/-- The `0 × 0` determinant is the empty product `1`. -/
theorem cofactorDetZeroSize {carrier : Type} (ring : CommutativeRingWitness carrier)
    (matrix : SetoidMatrix carrier) : cofactorDet ring 0 matrix = ring.one :=
  rfl

/-- The `1 × 1` determinant is its single entry. -/
theorem cofactorDetOneSize {carrier : Type} (ring : CommutativeRingWitness carrier)
    (matrix : SetoidMatrix carrier) :
    ring.denotesSame (cofactorDet ring 1 matrix) (matrix.entry 0 0) :=
  ring.denotesSameIsTransitive _ _ _
    (addZeroLeft ring (ring.mul (ring.mul ring.one (matrix.entry 0 0)) ring.one))
    (ring.denotesSameIsTransitive _ _ _
      (ring.oneIsRightMultiplicativeIdentity (ring.mul ring.one (matrix.entry 0 0)))
      (oneMulLeft ring (matrix.entry 0 0)))

/-- The minor of the identity at column `0` is the smaller identity. -/
theorem minorFirstRowOfIdentity {carrier : Type} (ring : CommutativeRingWitness carrier)
    (dimension : Nat) :
    DenoteSame ring (minorFirstRow (identityMatrix ring (dimension + 1)) 0)
      (identityMatrix ring dimension) :=
  { sameRowCount := rfl
    sameColCount := rfl
    entriesAgree := fun rowIndex colIndex =>
      denotesSameOfEq ring (iteSuccCondCollapse ring rowIndex colIndex) }

/-- The determinant of the identity matrix is `1`. -/
theorem cofactorDetIdentity {carrier : Type} (ring : CommutativeRingWitness carrier) (size : Nat) :
    ring.denotesSame (cofactorDet ring size (identityMatrix ring size)) ring.one :=
  match size with
  | 0 => ring.denotesSameIsReflexive ring.one
  | Nat.succ predecessor =>
      ring.denotesSameIsTransitive _ _ _
        (sumUpToCongr ring (Nat.succ predecessor)
          (fun colIndex _ =>
            ring.denotesSameIsTransitive _ _ _
              (mulSwapLastTwo ring (signAlternating ring colIndex)
                (if (0 : Nat) = colIndex then ring.one else ring.zero)
                (cofactorDet ring predecessor
                  (minorFirstRow (identityMatrix ring (Nat.succ predecessor)) colIndex)))
              (ring.mulRespectsDenotesSame _ _ _ _
                (ring.denotesSameIsReflexive
                  (ring.mul (signAlternating ring colIndex)
                    (cofactorDet ring predecessor
                      (minorFirstRow (identityMatrix ring (Nat.succ predecessor)) colIndex))))
                (denotesSameOfEq ring (iteOneZeroCondSymm ring 0 colIndex)))))
        (ring.denotesSameIsTransitive _ _ _
          (sumUpToDeltaRightPicks ring (Nat.succ predecessor)
            (fun colIndex =>
              ring.mul (signAlternating ring colIndex)
                (cofactorDet ring predecessor
                  (minorFirstRow (identityMatrix ring (Nat.succ predecessor)) colIndex)))
            0 (Nat.zero_lt_succ predecessor))
          (ring.denotesSameIsTransitive _ _ _
            (oneMulLeft ring
              (cofactorDet ring predecessor
                (minorFirstRow (identityMatrix ring (Nat.succ predecessor)) 0)))
            (ring.denotesSameIsTransitive _ _ _
              (cofactorDetCongr ring predecessor (minorFirstRowOfIdentity ring predecessor))
              (cofactorDetIdentity ring predecessor))))

end SetoidMatrix

end FX1Poly.ComputerAlgebra
