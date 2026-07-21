import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableKeystoneReduction
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithLandedMagnitudeEquivalence

/-! # SmithReachableMagnitudeResidual — the reachable residual as a decidable `Nat` magnitude equality

The corrected-driver totality reduces to the reachable divisibility scalar
`LandedPivotDividesMinorGcdReachable` (`landed ∣ gcd(minor)`).  With the shipped converse
`minorGcdDividesLanded` (`gcd ∣ landed`) that leg is equivalent to the magnitude equality
`|landed| = gcd(minor)`, named here `LandedAbsEqMinorGcdReachable`: a `Nat` equality decidable at every
concrete instance.  The module proves the two inter-derivable and re-routes the driver through the
equality.  The two-sided form is needed — `|landed| ≤ gcd` alone leaves the `landed = 0`, `gcd ≠ 0` case
unforced — and equal magnitudes divide each other by `dividesExactlyOfNatAbsEq`.

`SmithReduceCompleteDriverStatement` stays uninhabited hypothesis-free.  Given the shipped converse, the
only open half is the descent `|landed| ≤ gcd(minor)`, a structural `Nat.rec` induction (not
`WellFounded.fix`); the round-level chain `pivot(n+1) ∣ pivot(n)` is machine-refuted
(`smithFoldDescendsOnNonzeroPivotIsRefuted`) and is not assumed here.

Raw Lean 4 + `Init`, structural only.  ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-- After the pivot-`pivotIndex` clearing sweep, the landed pivot has magnitude equal to the input
`[pivotIndex, ·)` minor's gcd magnitude, over the reachable image `ReachableFromPhaseA`.  A `Nat`
equality, decidable at every concrete instance; the reachable transport of
`MinAbsEuclidLandsMinorGcdMagnitude` (`SmithLandedMagnitudeEquivalence`). -/
def LandedAbsEqMinorGcdReachable : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    ReachableFromPhaseA height width matrix pivotIndex →
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    ((matrix.applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs
      = (minorGcdWithin matrix pivotIndex height width).natAbs

/-- Feed the magnitude equality to `dividesExactlyOfNatAbsEq` (`|landed| = |gcd| ⟹ landed ∣ gcd`) to
obtain the divisibility scalar `LandedPivotDividesMinorGcdReachable`.  The two-sided equality closes the
`landed = 0`, `gcd ≠ 0` case that a one-sided `≤` leaves open. -/
theorem landedDividesMinorGcdReachableOfAbsEq
    (absEq : LandedAbsEqMinorGcdReachable) : LandedPivotDividesMinorGcdReachable := by
  intro matrix pivotIndex height width reached isRect pRowLt pColLt
  exact dividesExactlyOfNatAbsEq
    (absEq matrix pivotIndex height width reached isRect pRowLt pColLt)

/-- From the divisibility scalar (`landed ∣ gcd`) and the shipped converse `minorGcdDividesLanded`
(`gcd ∣ landed`), descend both to `natAbs` and close by `natDividesAntisymm`. -/
theorem landedAbsEqMinorGcdReachableOfDivides
    (landedDividesGcd : LandedPivotDividesMinorGcdReachable) : LandedAbsEqMinorGcdReachable := by
  intro matrix pivotIndex height width reached isRect pRowLt pColLt
  exact natDividesAntisymm
    (natDividesNatAbsOfIntDivides
      (landedDividesGcd matrix pivotIndex height width reached isRect pRowLt pColLt))
    (natDividesNatAbsOfIntDivides
      (minorGcdDividesLanded matrix pivotIndex height width isRect pRowLt pColLt))

/-- The two-way equivalence: given the shipped converse `gcd ∣ landed`, the divisibility scalar
`landed ∣ gcd` and the magnitude equality `|landed| = |gcd|` are inter-derivable — the same open content
in a decidable `Nat`-equality shape. -/
theorem landedDividesMinorGcdReachableIffAbsEq :
    LandedPivotDividesMinorGcdReachable ↔ LandedAbsEqMinorGcdReachable :=
  ⟨landedAbsEqMinorGcdReachableOfDivides, landedDividesMinorGcdReachableOfAbsEq⟩

/-- Compose the forward bridge `landedDividesMinorGcdReachableOfAbsEq` with the scalar driver
`smithReduceCompleteDriverOfLandedDividesMinorGcdReachable`.  `SmithReduceCompleteDriverStatement` is
inhabited given `LandedAbsEqMinorGcdReachable`, still under a hypothesis. -/
theorem smithReduceCompleteDriverOfLandedAbsEqMinorGcdReachable
    (absEq : LandedAbsEqMinorGcdReachable) : SmithReduceCompleteDriverStatement :=
  smithReduceCompleteDriverOfLandedDividesMinorGcdReachable
    (landedDividesMinorGcdReachableOfAbsEq absEq)

end FX1Poly.ComputerAlgebra
