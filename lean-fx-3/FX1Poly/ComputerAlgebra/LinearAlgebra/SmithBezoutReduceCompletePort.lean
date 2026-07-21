import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutRoundReachable

/-! # Smith-Bezout reduce-complete port

Scaffolding for the Bezout-drop divisibility driver: fuel domination, cross-clean maintenance,
single-position content invariance, and the mechanical reduction port.
`SmithReduceCompleteBezoutDriverStatement` and the earlier in-block variant remain uninhabited here.
The module reduces that mandate to one named residual, `SmithBezoutRepairInvariantsStatement`, the two
Phase-B invariants (window-diagonality and prefix chain) over the Bezout repair output; the reduction
port discharges Phase C internally. The genuinely open arcs -- fuel-adequacy find-`none` reachability
and the multi-position chain assembly -- are recorded as uninhabited Props rather than inhabited by a
weakened variant.

Raw Lean 4 on `Init`, structural only, ASCII identifiers, no `axiom`/`sorry`/`propext`/`Quot.sound`/
`Classical`/`omega`/`native_decide`/`WellFounded.fix`. Per-declaration zero-axiom gate in the
FX1PolyAudit twin. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

set_option maxRecDepth 100000

/-! ## Fuel domination: the descent measure sits below the per-position seed -/

/-- `pivotMagnitudeWithin matrix pivotIndex` (the descent measure `|diagonalEntryAt pivotIndex|`) is
bounded by `smithMinorAbsSum matrix pivotIndex height width`, the seed the Bezout position sweep is fed.
Instantiates `smithMinorEntryLeAbsSum` at the pivot witness `(pivotIndex, pivotIndex)`, so the seed
dominates the measure at every position. -/
theorem pivotMagnitudeWithinLeMinorAbsSum (matrix : IntMatrix) (pivotIndex height width : Nat)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    pivotMagnitudeWithin matrix pivotIndex ≤ smithMinorAbsSum matrix pivotIndex height width :=
  smithMinorEntryLeAbsSum matrix pivotIndex height width pivotIndex pivotIndex
    (Nat.le_refl pivotIndex)
    (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pRowLt)
    (Nat.le_refl pivotIndex)
    (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pColLt)

/-! ## Cross-clean maintenance: the clean-cross guard is a loop invariant -/

/-- One Bezout-drop round re-establishes the clean cross: its trailing letter is `smithCascadeSweep` at
the seed `smithMinorAbsSum afterClear`, whose output cross is clear by
`smithCascadeSweepSeedReachesCrossClear`. The staged matrices `afterFold`/`afterSign`/`afterClear` stay
rectangular under `applyOperationsPreservesRectangular`. Hence the clean-cross guard holds every round,
a loop invariant rather than a per-round assumption. -/
theorem smithBezoutRepairRoundAtFoundReEstablishesCrossClean
    (work : IntMatrix) (pivotIndex height width foundRow foundCol : Nat)
    (isRect : work.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    smithPivotCrossClean (smithBezoutRepairRoundAtFound work pivotIndex height width foundRow foundCol)
      pivotIndex height width := by
  let afterFold := work.addRowMultiple foundRow pivotIndex 1
  let afterSign := afterFold.applyOperations (smithSignNormalizeOps afterFold pivotIndex)
  let afterClear := afterSign.addColumnMultiple pivotIndex foundCol
    (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex) (afterSign.entryAt pivotIndex foundCol)))
  have afterFoldRect : afterFold.IsRectangular height width :=
    applyOperationsPreservesRectangular
      [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1)]
      work isRect
  have afterSignRect : afterSign.IsRectangular height width :=
    applyOperationsPreservesRectangular (smithSignNormalizeOps afterFold pivotIndex) afterFold afterFoldRect
  have afterClearRect : afterClear.IsRectangular height width :=
    applyOperationsPreservesRectangular
      [ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple pivotIndex foundCol
        (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex) (afterSign.entryAt pivotIndex foundCol))))]
      afterSign afterSignRect
  show smithCrossIsClear
      (afterClear.applyOperations
        (smithCascadeSweep (smithMinorAbsSum afterClear pivotIndex height width) afterClear pivotIndex
          height width))
      pivotIndex height width = true
  exact smithCascadeSweepSeedReachesCrossClear afterClear pivotIndex height width afterClearRect pRowLt pColLt

/-! ## Content invariance: the Bezout position sweep preserves the sub-block gcd -/

/-- Every letter of the Bezout-drop round word (found-row fold, sign normalisation, the single Bezout
column op, the trailing cascade) sits at indices `>= pivotIndex >= lo`. The fold source `foundRow` and
column target `foundCol` are `>= pivotIndex` from `smithFindNonDividingInBlockSomeProperties`; the sign
word via `smithSignNormalizeOpsBoundedBelow` and the cascade via `smithCascadeSweepBoundedBelow`. This
lets `minorGcdStableUnderBoundedWord` apply to the Bezout word. -/
theorem smithBezoutRepairRoundWordAtFoundBoundedBelow (lo : Nat) (work : IntMatrix)
    (pivotIndex height width foundRow foundCol : Nat)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (pivotGe : lo ≤ pivotIndex) (foundRowGe : lo ≤ foundRow) (foundColGe : lo ≤ foundCol) :
    allOpsBoundedBelow lo (smithBezoutRepairRoundWordAtFound work pivotIndex height width foundRow foundCol)
      = true := by
  refine allOpsBoundedBelowAppend lo _ _
    (allOpsBoundedBelowAppend lo _ _
      (allOpsBoundedBelowAppend lo _ _ ?_ ?_) ?_) ?_
  · exact boolAndBothTrue (opBoundedBelowAddRow lo foundRow pivotIndex 1 foundRowGe pivotGe) rfl
  · exact smithSignNormalizeOpsBoundedBelow _ lo pivotIndex
  · exact boolAndBothTrue (opBoundedBelowAddColumn lo pivotIndex foundCol _ pivotGe foundColGe) rfl
  · exact smithCascadeSweepBoundedBelow lo _ _ pivotIndex height width
      pivotRowInRange pivotColInRange pivotGe

/-- The whole Bezout position-sweep word is bounded below the pivot: the `none`-branch cascade and the
`some`-branch round word followed by the recursion all sit at indices `>= pivotIndex >= lo`. Structural
on `fuel`; the found position is `>= pivotIndex` (both coordinates) by
`smithFindNonDividingInBlockSomeProperties`. -/
theorem smithBezoutRepairPositionSweepBoundedBelow (lo : Nat) :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      pivotIndex < height → pivotIndex < width → lo ≤ pivotIndex →
      allOpsBoundedBelow lo (smithBezoutRepairPositionSweep fuel matrix pivotIndex height width) = true
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, matrix, pivotIndex, height, width, pivotRowInRange, pivotColInRange, pivotGe => by
      show allOpsBoundedBelow lo
          (match smithFindNonDividingInBlock matrix pivotIndex height width with
           | none =>
               smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                 height width
           | some (foundRow, foundCol) =>
               let roundWord :=
                 smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol
               roundWord ++ smithBezoutRepairPositionSweep fuel (matrix.applyOperations roundWord)
                 pivotIndex height width) = true
      cases hFind : smithFindNonDividingInBlock matrix pivotIndex height width with
      | none =>
          exact smithCascadeSweepBoundedBelow lo _ matrix pivotIndex height width
            pivotRowInRange pivotColInRange pivotGe
      | some foundPair =>
          obtain ⟨foundRow, foundCol⟩ := foundPair
          obtain ⟨pivotLeFoundRow, _, pivotLeFoundCol, _, _⟩ :=
            smithFindNonDividingInBlockSomeProperties matrix pivotIndex height width foundRow foundCol
              pivotRowInRange pivotColInRange hFind
          exact allOpsBoundedBelowAppend lo _ _
            (smithBezoutRepairRoundWordAtFoundBoundedBelow lo matrix pivotIndex height width foundRow foundCol
              pivotRowInRange pivotColInRange pivotGe (Nat.le_trans pivotGe pivotLeFoundRow)
              (Nat.le_trans pivotGe pivotLeFoundCol))
            (smithBezoutRepairPositionSweepBoundedBelow lo fuel _ pivotIndex height width
              pivotRowInRange pivotColInRange pivotGe)

/-- `minorGcdWithin` of the `[pivotIndex, .)^2` block is invariant across the Bezout position repair.
Boundedness (`smithBezoutRepairPositionSweepBoundedBelow` at `lo := pivotIndex`) feeds
`minorGcdStableUnderBoundedWord`, so the landed minor gcd equals the input minor gcd. -/
theorem smithBezoutRepairPositionSweepPreservesMinorGcd (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width) (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    minorGcdWithin
        (matrix.applyOperations
          (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width))
        pivotIndex height width
      = minorGcdWithin matrix pivotIndex height width :=
  minorGcdStableUnderBoundedWord _ matrix isRect
    (smithBezoutRepairPositionSweepBoundedBelow pivotIndex
      (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
      pRowLt pColLt (Nat.le_refl pivotIndex))

/-! ## Single-position landed characterization (bound on find-`none`) -/

/-- If the Bezout position sweep's landed pivot has whole-block find-`none`, then `|landed pivot| =
|gcd(input minor)|`. The bridge `smithFindNonDividingInBlockNoneIffDivisibleWithin` turns find-`none`
into whole-block divisibility, which `blockDivisibilityImpliesAbsEqMinorGcd` sends to `|landed| =
|gcd(landed minor)|`; `smithBezoutRepairPositionSweepPreservesMinorGcd` rewrites that to the input minor
gcd. Bound on the operational find-`none`, the Bezout-word twin of
`smithRepairInBlockLandedFindNoneAbsEqInputMinorGcd`. -/
theorem smithBezoutLandedFindNoneAbsEqInputMinorGcd (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width) (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (landedFindNone :
      smithFindNonDividingInBlock
          (matrix.applyOperations
            (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width))
          pivotIndex height width = none) :
    ((matrix.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs
      = (minorGcdWithin matrix pivotIndex height width).natAbs := by
  have landedRect :
      (matrix.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).IsRectangular height width :=
    applyOperationsPreservesRectangular _ matrix isRect
  have keystoneAtLanded := blockDivisibilityImpliesAbsEqMinorGcd
    (matrix.applyOperations
      (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
        matrix pivotIndex height width))
    pivotIndex height width landedRect
    ((smithFindNonDividingInBlockNoneIffDivisibleWithin _ pivotIndex height width landedRect).mp
      landedFindNone)
  rw [keystoneAtLanded,
    smithBezoutRepairPositionSweepPreservesMinorGcd matrix pivotIndex height width isRect pRowLt pColLt]

/-! ## Reduction port: the mandate from the two Phase-B invariants -/

/-- Applying `smithReduceCompleteBezout`'s certificate (`diagOps ++ repairOps ++ signOps`) splits into
the sign sweep over the Bezout repair output, by `applyOperationsAppend` twice. The Bezout-word twin of
`smithReduceCompleteApplied`. -/
theorem smithReduceCompleteBezoutApplied (matrix : IntMatrix) (height width : Nat) :
    matrix.applyOperations (smithReduceCompleteBezout matrix height width).operations
      = (((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
            (smithBezoutDivisibilityRepairSweep (Nat.min height width)
              (matrix.applyOperations (smithReduceTotal matrix height width).operations)
              0 height width)).applyOperations
          (smithDiagonalSignSweep (Nat.min height width)
            ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
              (smithBezoutDivisibilityRepairSweep (Nat.min height width)
                (matrix.applyOperations (smithReduceTotal matrix height width).operations)
                0 height width))
            0 height width)) := by
  show matrix.applyOperations
      ((smithReduceTotal matrix height width).operations
        ++ smithBezoutDivisibilityRepairSweep (Nat.min height width)
              (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width
        ++ smithDiagonalSignSweep (Nat.min height width)
              ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
                (smithBezoutDivisibilityRepairSweep (Nat.min height width)
                  (matrix.applyOperations (smithReduceTotal matrix height width).operations)
                  0 height width))
              0 height width) = _
  rw [applyOperationsAppend, applyOperationsAppend]

/-- The full Bezout-driver output has nonnegative diagonal at every window position. The applied output
splits off the sign phase (`smithReduceCompleteBezoutApplied`) over a rectangular `afterRepair`, and
`signSweepDiagonalNonnegReached` gives nonnegativity; no Bezout-specific invariant is needed. The
Bezout-word twin of `smithReduceCompleteDiagonalNonneg`. -/
theorem smithReduceCompleteBezoutDiagonalNonneg :
    ∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      ∀ position, position < Nat.min height width →
        0 ≤ (matrix.applyOperations
              (smithReduceCompleteBezout matrix height width).operations).diagonalEntryAt position := by
  intro matrix height width isRect position positionBelow
  show 0 ≤ (matrix.applyOperations
      (smithReduceCompleteBezout matrix height width).operations).entryAt position position
  rw [smithReduceCompleteBezoutApplied matrix height width]
  have afterDiagRect :
      (matrix.applyOperations (smithReduceTotal matrix height width).operations).IsRectangular height width :=
    applyOperationsPreservesRectangular (smithReduceTotal matrix height width).operations matrix isRect
  have afterRepairRect :
      ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
        (smithBezoutDivisibilityRepairSweep (Nat.min height width)
          (matrix.applyOperations (smithReduceTotal matrix height width).operations)
          0 height width)).IsRectangular height width :=
    applyOperationsPreservesRectangular _ _ afterDiagRect
  have positionBelowShifted : position < 0 + Nat.min height width :=
    (Nat.zero_add (Nat.min height width)).symm ▸ positionBelow
  have positionBelowHeight : position < height :=
    natLeTrans positionBelow (natMinLeLeft height width)
  exact signSweepDiagonalNonnegReached (Nat.min height width) _ 0 height width position
    afterRepairRect (natZeroLe position) positionBelowShifted positionBelowHeight positionBelow

/-- `SmithReduceCompleteBezoutDriverStatement` follows from two invariant obligations on the Bezout
repair output: window-diagonality at 0 and the full prefix chain. Phase C is discharged internally by
`smithReduceCompleteBezoutDiagonalNonneg`, and the sign phase carries window-diagonality and the chain
from `afterRepair` to the full output via `smithSignSweepPreservesWindowDiagonal` /
`smithSignSweepPreservesChain` composed with `smithReduceCompleteBezoutApplied`. The Bezout-word twin of
`smithReduceCompleteDriverOfRepairInvariants`. -/
theorem smithReduceCompleteBezoutDriverOfRepairInvariants
    (repairWindowDiagHolds : ∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      IsWindowDiagonal
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithBezoutDivisibilityRepairSweep (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        0 height width)
    (repairChainHolds : ∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      SmithChainPrefix
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithBezoutDivisibilityRepairSweep (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        (Nat.min height width) height width) :
    SmithReduceCompleteBezoutDriverStatement :=
  fun matrix height width isRect =>
    isSmithNormalFormOfWindowDiagonalChainNonneg
      (matrix.applyOperations (smithReduceCompleteBezout matrix height width).operations) height width
      (by
        have afterDiagRect :
            (matrix.applyOperations (smithReduceTotal matrix height width).operations).IsRectangular
              height width :=
          applyOperationsPreservesRectangular (smithReduceTotal matrix height width).operations matrix isRect
        have afterRepairRect :
            ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
              (smithBezoutDivisibilityRepairSweep (Nat.min height width)
                (matrix.applyOperations (smithReduceTotal matrix height width).operations)
                0 height width)).IsRectangular height width :=
          applyOperationsPreservesRectangular _ _ afterDiagRect
        rw [smithReduceCompleteBezoutApplied matrix height width]
        exact smithSignSweepPreservesWindowDiagonal (Nat.min height width) _ 0 height width
          afterRepairRect (repairWindowDiagHolds matrix height width isRect))
      (smithReduceCompleteBezoutDiagonalNonneg matrix height width isRect)
      (by
        have afterDiagRect :
            (matrix.applyOperations (smithReduceTotal matrix height width).operations).IsRectangular
              height width :=
          applyOperationsPreservesRectangular (smithReduceTotal matrix height width).operations matrix isRect
        have afterRepairRect :
            ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
              (smithBezoutDivisibilityRepairSweep (Nat.min height width)
                (matrix.applyOperations (smithReduceTotal matrix height width).operations)
                0 height width)).IsRectangular height width :=
          applyOperationsPreservesRectangular _ _ afterDiagRect
        rw [smithReduceCompleteBezoutApplied matrix height width]
        exact smithSignSweepPreservesChain _ height width
          afterRepairRect (repairChainHolds matrix height width isRect))

/-! ## The invariants gate and the fuel-adequacy residual (recorded, uninhabited) -/

/-- The two Phase-B invariants over the Bezout repair output: window-diagonality at 0 and the full
prefix chain (the conjunction of `smithReduceCompleteBezoutDriverOfRepairInvariants`'s two hypotheses).
Uninhabited here; once inhabited the mandate fires by
`smithReduceCompleteBezoutMandateReducesToInvariants`. It decomposes into the fuel-adequacy find-`none`
(`SmithBezoutRepairPositionSweepReachesFindNoneStatement`), the per-position characterization
(`smithBezoutLandedFindNoneAbsEqInputMinorGcd`), and the multi-position chain assembly. -/
def SmithBezoutRepairInvariantsStatement : Prop :=
  (∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      IsWindowDiagonal
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithBezoutDivisibilityRepairSweep (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        0 height width)
    ∧
  (∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      SmithChainPrefix
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithBezoutDivisibilityRepairSweep (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        (Nat.min height width) height width)

/-- `SmithReduceCompleteBezoutDriverStatement` is inhabited as soon as
`SmithBezoutRepairInvariantsStatement` is, by feeding its two conjuncts through
`smithReduceCompleteBezoutDriverOfRepairInvariants`. -/
theorem smithReduceCompleteBezoutMandateReducesToInvariants
    (invariants : SmithBezoutRepairInvariantsStatement) :
    SmithReduceCompleteBezoutDriverStatement :=
  smithReduceCompleteBezoutDriverOfRepairInvariants invariants.1 invariants.2

/-- The fueled Bezout position sweep at its seed `smithMinorAbsSum` reaches find-`none` on a
rectangular, clean-cross state. The intended route is structural on fuel with `pivotMagnitudeWithin` as
the decreasing witness (bounded by the seed via `pivotMagnitudeWithinLeMinorAbsSum`), threading the
maintenance `smithBezoutRepairRoundAtFoundReEstablishesCrossClean` so the clean-cross guard is a loop
invariant. Uninhabited here; the open sub-obligations are positivity maintenance (find-`some` implies a
positive pivot on the reachable class) and trailing-cascade-preserves-`none`. Once inhabited it feeds
the per-position characterization `smithBezoutLandedFindNoneAbsEqInputMinorGcd` toward the invariants. -/
def SmithBezoutRepairPositionSweepReachesFindNoneStatement : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    smithPivotCrossClean matrix pivotIndex height width →
    smithFindNonDividingInBlock
        (matrix.applyOperations
          (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width))
        pivotIndex height width = none

end FX1Poly.ComputerAlgebra
