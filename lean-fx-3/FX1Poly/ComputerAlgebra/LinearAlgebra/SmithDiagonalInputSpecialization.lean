import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedChainReduction

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithDiagonalInputSpecialization — the diagonal-input
    specialization of the Smith keystone (H2-SMITH r24, #2261)

The r22–r23 arc collapsed the corrected-driver totality
(`SmithReduceCompleteDriverStatement`) onto the SINGLE residual
`SmithCascadeLandedPivotDividesMinor`: the pivot-`p` clearing position sweep lands, at the pivot,
a divisor of every entry of the input's `[p, ·)` minor (the "min-abs Euclid cascade computes the
gcd" fact — a standalone major arc).

r24 asks whether SPECIALIZING that keystone to DIAGONAL inputs — the shape the Phase-A output
provably has (`smithReduceTotalSweepDiagonalizes`) — closes the chain.  The verdict, machine-adjudicated
here, is **NO** (recon fill-in-region verdict (iii)):

  * On a window-diagonal input the keystone's INPUT off-diagonal cells are all `0` (divisible by
    anything), so the keystone-input-minor divisibility collapses to the DIAGONAL half alone
    (`matrixEntriesDivisibleByWithinOfDiagonalInput`) — a genuine narrowing.
  * But `chainWindowedThroughPivots` (NODE A of the shipped reduction) invokes the keystone on the
    ADVANCED matrix at every pivot `p ≥ 1`, and the advanced matrix is generally NON-diagonal:
    `smithDiagonalInputPivotOneInputNotWindowDiagonal` machine-refutes window-diagonality of the
    pivot-0 sweep output of `diag(15, 10, 6, 4)` at floor `1` (its `[1, ·)` minor carries `-20` at
    `(3, 1)`).  So the diagonal-input specialization discharges ONLY the pivot-0 evaluation and does
    NOT re-plumb the chain.

This file also ships the pure PAIRWISE-GCD contract (`IntPairwiseGcdSpec`, the cash-out of the shipped
Euclid induction) and the ITERATED-pairwise-gcd common-divisor fact (`intGcdFoldrDividesAll`), which is
the ARITHMETIC half of the diagonal-common-divisor obligation.  The surviving residual remains
`SmithCascadeLandedPivotDividesMinor` (the cascade lands the diagonal gcd), OPEN.

## Zero-axiom

`by decide` on small `Int`/matrix literals (independently `#print axioms`-clean), structural
`List.foldr` recursion, `∃`-witness arithmetic over the shipped `intGcd*` / `intMulAssoc` /
`entryAtBeyondZero` / `matrixEntriesDivisibleByWithinOfHalves`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithDiagonalInputSpecialization.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## BRICK 1 — the pairwise-gcd contract + the eval truth-probes (H2-SMITH r24, B1)

The pairwise gcd `intGcd a b` and all its structural facts are SHIPPED (`IntGreatestCommonDivisor`,
riding the counting-Euclid induction `natGcdWithFuelDividesBoth` / `natGcdBezout`).  B1 truth-probes
the values on the recon battery FIRST (by `decide`), then bundles the shipped facts into ONE reusable
contract `IntPairwiseGcdSpec` (nonnegative common divisor, greatest).  The magnitude-descent half of
the contract is the SHIPPED `smithRepairDecreasesPivotSize`
(`(intGcd a b).natAbs < a.natAbs` when `0 < a.natAbs ∧ a ∤ b`); it is conditional, so it stays a
companion rather than an unconditional field. -/

/-- Pairwise gcd of the NODE-A fold operands: `gcd(15, 10) = 5`. -/
theorem intGcdFifteenTen : intGcd 15 10 = 5 := by decide

/-- Pairwise gcd of the concrete gcd > 1 window pivot pair: `gcd(6, 10) = 2`. -/
theorem intGcdSixTen : intGcd 6 10 = 2 := by decide

/-- Zero-pivot bootstrap: `gcd(0, 4) = 4` — `0` contributes nothing, the gcd is the other magnitude. -/
theorem intGcdZeroFour : intGcd 0 4 = 4 := by decide

/-- Both-negative pair: signs fold into magnitudes, `gcd(-6, -4) = 2`. -/
theorem intGcdNegSixNegFour : intGcd (-6) (-4) = 2 := by decide

/-- Mixed-sign pair: `gcd(6, -4) = 2` (the nonnegative representative). -/
theorem intGcdSixNegFour : intGcd 6 (-4) = 2 := by decide

/-- Negative-left pair: `gcd(-15, 10) = 5`. -/
theorem intGcdNegFifteenTen : intGcd (-15) 10 = 5 := by decide

/-- **The pairwise-gcd contract over `Int`** — `intGcd a b` is a NONNEGATIVE common divisor of the
pair that is GREATEST (every common divisor divides it).  The reusable cash-out of the shipped
counting-Euclid induction; the conditional magnitude-descent half is the companion
`smithRepairDecreasesPivotSize`. -/
structure IntPairwiseGcdSpec (leftValue rightValue : Int) : Prop where
  /-- The gcd is nonnegative (the canonical sign choice). -/
  isNonnegative : (0 : Int) ≤ intGcd leftValue rightValue
  /-- The gcd divides the left argument. -/
  dividesLeft : IntDivides (intGcd leftValue rightValue) leftValue
  /-- The gcd divides the right argument. -/
  dividesRight : IntDivides (intGcd leftValue rightValue) rightValue
  /-- Every common divisor of the pair divides the gcd. -/
  isGreatest : ∀ {commonDivisor : Int}, IntDivides commonDivisor leftValue →
    IntDivides commonDivisor rightValue → IntDivides commonDivisor (intGcd leftValue rightValue)

/-- **`intGcd` satisfies the pairwise-gcd contract** — assembles the shipped `intGcdIsNonnegative`,
`intGcdDividesLeft`, `intGcdDividesRight`, `intGcdGreatest` into the single contract object.  A
`∀ a b`-theorem to fire on the battery. -/
theorem intGcdSatisfiesPairwiseSpec (leftValue rightValue : Int) :
    IntPairwiseGcdSpec leftValue rightValue :=
  ⟨intGcdIsNonnegative leftValue rightValue,
   intGcdDividesLeft leftValue rightValue,
   intGcdDividesRight leftValue rightValue,
   fun dividesLeft dividesRight => intGcdGreatest dividesLeft dividesRight⟩

/-! ## BRICK 2 — the diagonal-input narrowing + the re-plumb refutation (H2-SMITH r24, B2)

The verdict-(iii) content.  On a WINDOW-DIAGONAL input the keystone's INPUT off-diagonal cells are
`0`, so its off-diagonal half is free — the keystone-input-minor divisibility narrows to the DIAGONAL
common-divisor obligation alone.  But this specialization discharges ONLY the pivot-0 evaluation (the
Phase-A output is provably window-diagonal); the chain carrier `chainWindowedThroughPivots` needs the
keystone on the pivot-`p ≥ 1` ADVANCED matrices, which are NON-diagonal — machine-refuted below. -/

/-- **On a window-diagonal input the off-diagonal half is free.**  Every off-diagonal cell of the
`[lo, ·)²` quadrant of a window-diagonal rectangular matrix is `0` (in-window by `IsWindowDiagonal`,
beyond-window by `entryAtBeyondZero`), hence divisible by ANY `divisor`.  The narrowing that removes
the seed's gcd-ideal wall on diagonal inputs. -/
theorem subBlockOffDiagonalDivisibleOfWindowDiagonal {height width : Nat} (divisor : Int)
    (matrix : IntMatrix) (isRect : matrix.IsRectangular height width) (lo : Nat)
    (isDiag : IsWindowDiagonal matrix lo height width) :
    SubBlockOffDiagonalDivisibleFrom divisor lo matrix := by
  intro rowIndex colIndex rowGe colGe rowNeCol
  cases Nat.lt_or_ge rowIndex height with
  | inl rowLt =>
      cases Nat.lt_or_ge colIndex width with
      | inl colLt =>
          rw [isDiag rowIndex colIndex rowGe rowLt colGe colLt rowNeCol]
          exact dividesExactlyZero divisor
      | inr colGeWidth =>
          rw [entryAtBeyondZero matrix isRect rowIndex colIndex (Or.inr colGeWidth)]
          exact dividesExactlyZero divisor
  | inr rowGeHeight =>
      rw [entryAtBeyondZero matrix isRect rowIndex colIndex (Or.inl rowGeHeight)]
      exact dividesExactlyZero divisor

/-- **The keystone-input-minor divisibility from the DIAGONAL half alone, on a diagonal input.**
Given a window-diagonal rectangular input, `MatrixEntriesDivisibleByWithin divisor lo matrix` (the
keystone's input-minor obligation) follows from the diagonal-common-divisor obligation
`SubBlockDiagonalDivisibleFrom divisor lo matrix` — the off-diagonal half is supplied for free by
`subBlockOffDiagonalDivisibleOfWindowDiagonal`.  The genuine narrowing of the keystone on diagonal
inputs (recon verdict (iii)). -/
theorem matrixEntriesDivisibleByWithinOfDiagonalInput {height width : Nat} (divisor : Int)
    (matrix : IntMatrix) (isRect : matrix.IsRectangular height width) (lo : Nat)
    (isDiag : IsWindowDiagonal matrix lo height width)
    (diagDivisible : SubBlockDiagonalDivisibleFrom divisor lo matrix) :
    MatrixEntriesDivisibleByWithin divisor lo matrix :=
  matrixEntriesDivisibleByWithinOfHalves divisor lo matrix diagDivisible
    (subBlockOffDiagonalDivisibleOfWindowDiagonal divisor matrix isRect lo isDiag)

/-- **The diagonal-input-scoped keystone** — the `SmithCascadeLandedPivotDividesMinor` obligation
RESTRICTED to window-diagonal inputs, and further NARROWED to its diagonal-common-divisor content:
on a window-diagonal input, the pivot-`p` clearing-sweep landed pivot divides every INPUT DIAGONAL
entry of the `[p, ·)` window.  Strictly weaker than the unrestricted keystone (it only sees diagonal
inputs), and — per `smithDiagonalInputPivotOneInputNotWindowDiagonal` — NOT enough to feed
`chainWindowedThroughPivots`. -/
def SmithDiagonalInputLandedPivotDividesDiagonal : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    IsWindowDiagonal matrix pivotIndex height width →
    SubBlockDiagonalDivisibleFrom
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      pivotIndex
      matrix

/-- **The re-threaded reduction (a Lean theorem)** — GIVEN the diagonal-input-scoped keystone, the
FULL keystone-input-minor divisibility `MatrixEntriesDivisibleByWithin (landed pivot) pivotIndex matrix`
holds ON window-diagonal inputs.  Composes the scoped diagonal obligation with the diagonal-input
narrowing `matrixEntriesDivisibleByWithinOfDiagonalInput`.  This is the pivot-0 evaluation of the
keystone (the Phase-A output being window-diagonal, `phaseAOutputIsWindowDiagonalAtZero`); it does NOT
generalise to the chain (the advanced matrices are non-diagonal). -/
theorem landedPivotDividesMinorOnDiagonalInput
    (diagonalCase : SmithDiagonalInputLandedPivotDividesDiagonal)
    (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (isDiag : IsWindowDiagonal matrix pivotIndex height width) :
    MatrixEntriesDivisibleByWithin
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      pivotIndex
      matrix :=
  matrixEntriesDivisibleByWithinOfDiagonalInput _ matrix isRect pivotIndex isDiag
    (diagonalCase matrix pivotIndex height width isRect pRowLt pColLt isDiag)

/-- **The Phase-A output is window-diagonal at floor `0`** — the total cross-clear sweep output has an
off-diagonal-zero `[0, ·)` window (`smithReduceTotalSweepDiagonalizes`, the `0 ≤ ·` guards trivial).
So at pivot `0` the diagonal-input hypothesis of the scoped keystone is DISCHARGED, not assumed. -/
theorem phaseAOutputIsWindowDiagonalAtZero (matrix : IntMatrix) (height width : Nat)
    (isRect : matrix.IsRectangular height width) :
    IsWindowDiagonal
      (matrix.applyOperations (smithReduceTotalSweep (Nat.min height width) matrix 0 height width))
      0 height width :=
  fun rowIndex colIndex _rowGe rowLt _colGe colLt rowNeCol =>
    smithReduceTotalSweepDiagonalizes matrix height width isRect rowIndex colIndex rowLt colLt rowNeCol

/-- The NODE-E re-plumb fixture `diag(15, 10, 6, 4)` — the pivot-0 clearing sweep sends its `(3, 1)`
cell to `-20`, planting a nonzero off-diagonal INSIDE the pivot-1 window `[1, ·)²`. -/
def smithDiagonalInputReplumbFixture : IntMatrix :=
  { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] }

set_option maxRecDepth 8000 in
/-- **THE RE-PLUMB REFUTATION (verdict (iii), machine-checked).**  The pivot-0 clearing-sweep output
of `diag(15, 10, 6, 4)` is NOT window-diagonal at floor `1`: its `[1, ·)` minor carries `-20` at the
off-diagonal cell `(3, 1)` (`1 ≤ 3 < 4`, `1 ≤ 1 < 4`, `3 ≠ 1`).  So `chainWindowedThroughPivots`,
whose induction advances `matrix := matrix.applyOperations (pivot-0 sweep)` and would need
`IsWindowDiagonal (advanced) 1 · ·` to invoke the diagonal-input keystone at pivot 1, CANNOT obtain
it — the diagonal-input specialization discharges only pivot 0 and does NOT re-plumb the chain.  A
single-entry 4×4 sweep read (NODE-E granularity, within the defeq ceiling). -/
theorem smithDiagonalInputPivotOneInputNotWindowDiagonal :
    ¬ IsWindowDiagonal
        (smithDiagonalInputReplumbFixture.applyOperations
          (smithRepairPositionSweepClearing
            (smithMinorAbsSum smithDiagonalInputReplumbFixture 0 4 4)
            smithDiagonalInputReplumbFixture 0 4 4))
        1 4 4 :=
  fun isDiag =>
    absurd (isDiag 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

/-! ## BRICK 3 — the iterated pairwise gcd is a common divisor of the whole list (H2-SMITH r24, B3)

On a DIAGONAL input the pivot sweep's diagonal-common-divisor obligation is "the landed pivot divides
each diagonal entry `a_p … a_{n-1}`".  On the honest domain (the diagonal is fixed once diagonalised)
the value that divides all of them is the ITERATED pairwise gcd `foldr intGcd 0 [a_p, …]`.  This brick
ships the ARITHMETIC half — the iterated pairwise gcd IS a common divisor of every list element —
independent of the cascade.  The remaining gap (the CASCADE's landed pivot equals this fold) is the
open keystone, NOT arithmetic (recon Δ3: the fold does NOT compute the pairwise gcd of its two operands,
only the whole-minor min-abs descent lands the diagonal gcd). -/

/-- **Transitivity of `IntDivides`** — `a | b` and `b | c` compose to `a | c`; the cofactors multiply
through `intMulAssoc`.  The step the iterated-gcd fold rides. -/
theorem intDividesTrans {leftValue midValue rightValue : Int}
    (leftDividesMid : IntDivides leftValue midValue)
    (midDividesRight : IntDivides midValue rightValue) :
    IntDivides leftValue rightValue :=
  match leftDividesMid, midDividesRight with
  | ⟨leftCofactor, midEquation⟩, ⟨midCofactor, rightEquation⟩ =>
      ⟨leftCofactor * midCofactor,
        rightEquation.trans
          ((congrArg (· * midCofactor) midEquation).trans
            (intMulAssoc leftValue leftCofactor midCofactor))⟩

/-- **A common divisor of a whole list** — `divisor` divides every entry, as a structural conjunction
(`True` at the empty list).  The honest-domain diagonal-common-divisor predicate for an iterated fold. -/
def IntDividesAll (divisor : Int) : List Int → Prop
  | [] => True
  | head :: tail => IntDivides divisor head ∧ IntDividesAll divisor tail

/-- **`IntDividesAll` is monotone under divisor descent** — if `newDivisor | oldDivisor` and
`oldDivisor` divides every entry, then `newDivisor` divides every entry.  Transitivity lifted pointwise
over the list, structural on the list. -/
theorem intDividesAllMono {newDivisor oldDivisor : Int}
    (newDividesOld : IntDivides newDivisor oldDivisor) :
    ∀ {values : List Int}, IntDividesAll oldDivisor values → IntDividesAll newDivisor values
  | [], _ => trivial
  | _ :: _, ⟨headDivisible, tailDivisible⟩ =>
      ⟨intDividesTrans newDividesOld headDivisible, intDividesAllMono newDividesOld tailDivisible⟩

/-- **The iterated pairwise gcd is a common divisor of the whole list** — `foldr intGcd 0 values`
divides every entry of `values`.  Structural on the list: the head is divided by `intGcdDividesLeft`,
the tail by the inductive common divisor pushed down through `intGcdDividesRight` +
`intDividesAllMono`.  The arithmetic content of "the sweep computes the diagonal gcd" on the honest
domain (the value; NOT the claim that the cascade lands it — that is the open keystone). -/
theorem intGcdFoldrDividesAll :
    ∀ values : List Int, IntDividesAll (List.foldr intGcd 0 values) values
  | [] => trivial
  | head :: tail =>
      ⟨intGcdDividesLeft head (List.foldr intGcd 0 tail),
       intDividesAllMono (intGcdDividesRight head (List.foldr intGcd 0 tail))
         (intGcdFoldrDividesAll tail)⟩

/-- **The iterated pairwise gcd lands the diagonal gcd `2` on the concrete gcd > 1 window** —
`foldr intGcd 0 [6, 10, 8] = 2`, matching the CASCADE's landed pivot `2` on `diag(6, 10, 8)`
(`smithClearingSweepLandsMinorGcdOnConcreteWindow`).  The n = 3 honest-domain tie. -/
theorem intGcdFoldrLandsDiagonalGcdOnConcreteWindow : List.foldr intGcd 0 [6, 10, 8] = 2 := by decide

/-- **The concrete diagonal-common-divisor fact** — `2` divides every diagonal entry `6, 10, 8`, read
off `intGcdFoldrDividesAll [6, 10, 8]` at the reduced fold value `2` (defeq).  The arithmetic half of
the diagonal-input keystone at pivot 0 on `diag(6, 10, 8)`, fired from the general `∀`-theorem. -/
theorem intGcdFoldrDividesDiagonalOnConcreteWindow : IntDividesAll (2 : Int) [6, 10, 8] :=
  intGcdFoldrDividesAll [6, 10, 8]

/-! ## BRICK 4 — THE ASSEMBLY: the pivot-0 firing + the honest ledger (H2-SMITH r24, B4)

Per verdict (iii) the chain does NOT close.  What r24 DELIVERS as the assembly is the PIVOT-0 FIRING:
the diagonal-input-scoped keystone discharges the keystone-input-minor divisibility on the Phase-A
output HYPOTHESIS-FREE in the diagonal condition (the Phase-A output is provably window-diagonal), for
ANY rectangular input.  It stays conditional on the diagonal-common-divisor obligation
`SmithDiagonalInputLandedPivotDividesDiagonal`, which is OPEN.  NO hypothesis-free inhabitant of
`SmithReduceCompleteDriverStatement` is produced — that would repeat the r19 error. -/

/-- **THE PIVOT-0 FIRING (the assembly).**  GIVEN the diagonal-input-scoped keystone, the keystone's
input-minor divisibility holds on the Phase-A output at pivot `0`, with the diagonal-input hypothesis
DISCHARGED by the shipped `phaseAOutputIsWindowDiagonalAtZero` (the Phase-A output is window-diagonal).
The honest positive content of r24: the diagonal-input specialization COVERS pivot 0 for any
rectangular input.  It does NOT lift to pivots `≥ 1`
(`smithDiagonalInputPivotOneInputNotWindowDiagonal`), so it does NOT close
`SmithReduceCompleteDriverStatement`. -/
theorem landedPivotDividesMinorOnPhaseAOutputAtZero
    (diagonalCase : SmithDiagonalInputLandedPivotDividesDiagonal)
    (matrix : IntMatrix) (height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (heightPos : 0 < height) (widthPos : 0 < width) :
    MatrixEntriesDivisibleByWithin
      (((matrix.applyOperations
              (smithReduceTotalSweep (Nat.min height width) matrix 0 height width)).applyOperations
          (smithRepairPositionSweepClearing
            (smithMinorAbsSum
              (matrix.applyOperations
                (smithReduceTotalSweep (Nat.min height width) matrix 0 height width))
              0 height width)
            (matrix.applyOperations
              (smithReduceTotalSweep (Nat.min height width) matrix 0 height width))
            0 height width)).diagonalEntryAt 0)
      0
      (matrix.applyOperations
        (smithReduceTotalSweep (Nat.min height width) matrix 0 height width)) :=
  landedPivotDividesMinorOnDiagonalInput diagonalCase
    (matrix.applyOperations (smithReduceTotalSweep (Nat.min height width) matrix 0 height width))
    0 height width
    (applyOperationsPreservesRectangular _ matrix isRect)
    heightPos widthPos
    (phaseAOutputIsWindowDiagonalAtZero matrix height width isRect)

/-! ## The r24 arc ledger (H2-SMITH r24, #2261) — the diagonal-input specialization does NOT close

**What r24 shipped (all zero-axiom, additive; the r18–r23 world byte-intact).**

  * B1 — THE PAIRWISE-GCD CONTRACT.  The pairwise gcd values are truth-probed on the recon battery
    (`intGcdFifteenTen … intGcdNegFifteenTen`, all `decide`, independently `#print axioms`-clean), and
    the shipped counting-Euclid facts are bundled into `IntPairwiseGcdSpec` (nonnegative, divides both,
    greatest) with inhabitant `intGcdSatisfiesPairwiseSpec`.  The conditional magnitude-descent half is
    the shipped `smithRepairDecreasesPivotSize`.

  * B2 — THE NARROWING + THE RE-PLUMB REFUTATION.  On a window-diagonal input the keystone's
    off-diagonal half is free (`subBlockOffDiagonalDivisibleOfWithin`-style
    `subBlockOffDiagonalDivisibleOfWindowDiagonal`), so the keystone-input-minor divisibility narrows
    to the diagonal common-divisor obligation alone (`matrixEntriesDivisibleByWithinOfDiagonalInput`).
    The scoped keystone `SmithDiagonalInputLandedPivotDividesDiagonal` + its reduction
    `landedPivotDividesMinorOnDiagonalInput` cover the pivot-0 evaluation
    (`phaseAOutputIsWindowDiagonalAtZero`).  `smithDiagonalInputPivotOneInputNotWindowDiagonal`
    machine-refutes the re-plumb: `diag(15, 10, 6, 4)`'s pivot-0 sweep output is NOT window-diagonal at
    floor `1` (`(3, 1) = -20`), so `chainWindowedThroughPivots` cannot invoke the diagonal-input
    keystone at pivot `≥ 1`.

  * B3 — THE ITERATED PAIRWISE GCD.  `intGcdFoldrDividesAll` proves the iterated pairwise gcd
    `foldr intGcd 0 values` is a common divisor of every entry (the ARITHMETIC half of the
    diagonal-common-divisor obligation).  Δ3 (recon): the fold does NOT compute the pairwise gcd of its
    two operands — only the whole-minor min-abs descent lands the diagonal gcd — so this arithmetic
    fact does NOT by itself say the cascade lands it.

  * B4 — THE PIVOT-0 FIRING.  `landedPivotDividesMinorOnPhaseAOutputAtZero`: the diagonal-input
    specialization discharges the keystone at pivot 0 for ANY rectangular input, the diagonal condition
    supplied by the shipped Phase-A diagonalization.

**THE EXACT SURVIVING GOAL, named (NOT a fabricated flip).**  `SmithReduceCompleteDriverStatement` is
NOT inhabited hypothesis-free.  [r33: residual 1 below — the UNRESTRICTED keystone — is now REFUTED AS
STATED (`SmithLandedMagnitudeRefuted`, seed `[[0,6,0],[0,0,10],[0,0,0]]` lands `6` vs minor gcd `2`), NOT
merely OPEN; the machine-refuted non-diagonality of the advanced matrices noted in residual 1 is exactly
why.  Residual 2 (the diagonal-input evaluation) stays OPEN and is the honest surviving content.]  Two
nested residuals survive:

  1. `SmithCascadeLandedPivotDividesMinor` (the shipped r22 residual) — the UNRESTRICTED keystone the
     driver totality rests on (`smithReduceCompleteDriverOfLandedPivotDividesMinor`).  The
     diagonal-input specialization does NOT supply it: the chain needs it on the pivot-`≥ 1` ADVANCED
     matrices, which are non-diagonal (machine-refuted).

  2. `SmithDiagonalInputLandedPivotDividesDiagonal` (this round's scoped residual) — even the
     diagonal-input evaluation of the keystone (the diagonal-common-divisor obligation "the landed
     pivot divides each INPUT diagonal entry") is OPEN.  B3 discharges its ARITHMETIC half (the iterated
     pairwise gcd IS a common divisor of the diagonal); the surviving content is the cascade-output-value
     fact "the landed pivot equals the diagonal gcd = `foldr intGcd 0 [a_p, …]`" — a min-abs-descent
     correctness statement, the r11+ wall, decisively NOT r24-sized.

**Honest verdict.**  r24 narrows the keystone on diagonal inputs and covers pivot 0, but the
diagonal-input specialization CANNOT re-plumb the chain (verdict (iii), machine-adjudicated).  The
driver stays open; the surviving arithmetic goal is the cascade-lands-the-diagonal-gcd correctness.  No
flip is fabricated; `smithReduceFull`, its refutation, the certificate API, and the r18–r23 world stay
byte-intact (additive only). -/

end FX1Poly.ComputerAlgebra
