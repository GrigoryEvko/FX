import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutRoundReachable

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithBezoutReduceCompletePort — the Bezout-drop driver's
    mandate scaffolding: fuel domination, cross-clean maintenance, single-position content invariance
    + K2, and the mechanical reduction port (H2-SMITH r48, #2261)

## ★★ MANDATE STATUS: NOT FIRED — HONEST CUT (residuals named for r49) ★★

`SmithReduceCompleteBezoutDriverStatement` (`SmithBezoutRoundReachable`) stays UNINHABITED in r48, and so
does the original `SmithReduceCompleteInBlockDriverStatement` — both byte-intact.  The #2261 mandate needs
FOUR pieces glued: (A) K1 lifted to fuel adequacy (the fueled Bezout sweep REACHES find-`none`), (B) the
single-position landed characterization K2, (C) the multi-position chain assembly, (D) the mechanical
reduction port.  This round ships the MECHANICAL scaffolding and the single-position K2 hypothesis-bound
on the landed find-`none`, and reduces the whole mandate to ONE named residual Prop
`SmithBezoutRepairInvariantsStatement` (the two Phase-B invariants over the Bezout repair output).  The
genuinely-open arcs — fuel-adequacy positivity-maintenance (α) + trailing-cascade-preserves-`none` (β),
and the word-tied multi-position chain port — are NAMED LOUDLY below and stay UNINHABITED.  NOTHING here
inhabits a weakened variant and calls it the mandate.

## What r48 ships (all additive; consumes shipped r44/r45/r47 levers; zero fabrication)

  * **Fuel domination** `pivotMagnitudeWithinLeMinorAbsSum` — the K1 measure `pivotMagnitudeWithin` is
    dominated by the per-position seed `smithMinorAbsSum` (from `smithMinorEntryLeAbsSum` at the pivot).
    So the seed the driver actually feeds the position sweep provably bounds the descent measure.
  * **Cross-clean maintenance** `smithBezoutRepairRoundAtFoundReEstablishesCrossClean` — one Bezout-drop
    round RE-ESTABLISHES the clean cross (the K1 guard is a LOOP INVARIANT, not a per-round assumption).
    Rides the shipped `smithCascadeSweepSeedReachesCrossClear` on the round's trailing cascade.
  * **Content invariance** `smithBezoutRepairRoundWordAtFoundBoundedBelow` +
    `smithBezoutRepairPositionSweepBoundedBelow` + `smithBezoutRepairPositionSweepPreservesMinorGcd` —
    every Bezout-round letter is bounded below the pivot, so `minorGcdStableUnderBoundedWord` (r43) makes
    the position sweep INVARIANT on the sub-block gcd.
  * **K2 single-position** `smithBezoutLandedFindNoneAbsEqInputMinorGcd` — IF the Bezout sweep's landed
    pivot has whole-block find-`none` THEN `|landed pivot| = |gcd(INPUT minor)|`.  The r45 iff bridge +
    r44 keystone + content invariance, hypothesis-bound on the operational landing test.
  * **Reduction port** `smithReduceCompleteBezoutApplied` + `smithReduceCompleteBezoutDiagonalNonneg` +
    `smithReduceCompleteBezoutDriverOfRepairInvariants` — the mandate follows from the TWO Phase-B
    invariants on the Bezout repair output (window-diagonal + chain); Phase C is discharged internally.
  * **The r49 gate** `SmithBezoutRepairInvariantsStatement` (recorded, UNINHABITED) + the reducer
    `smithReduceCompleteBezoutMandateReducesToInvariants`: the mandate is now
    `SmithBezoutRepairInvariantsStatement → SmithReduceCompleteBezoutDriverStatement`.
  * **The fuel-adequacy residual** `SmithBezoutRepairPositionSweepReachesFindNoneStatement` (recorded,
    UNINHABITED) — the (α)+(β) arc feeding the invariants via the per-position K2.

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`/`WellFounded.fix`.  ASCII identifiers.  ADDITIVE only — the r18-r47 world is byte-intact.
Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutReduceCompletePort.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

set_option maxRecDepth 100000

/-! ## Brick 1 — fuel domination: the K1 measure sits below the per-position seed -/

/-- **The pivot magnitude is dominated by the minor abs-sum seed** — `pivotMagnitudeWithin matrix
pivotIndex` (`= |diagonalEntryAt pivotIndex|`, the K1 descent measure) is `≤ smithMinorAbsSum matrix
pivotIndex height width`, the STATIC fuel the Bezout position sweep is actually seeded with (at
`smithBezoutDivisibilityRepairSweep`).  Instantiates the shipped `smithMinorEntryLeAbsSum` at the pivot
witness `(pivotIndex, pivotIndex)`, in range by `natLtAddSubOfLt`.  So the seed provably dominates the
measure — the fuel-adequacy base is met at every position. -/
theorem pivotMagnitudeWithinLeMinorAbsSum (matrix : IntMatrix) (pivotIndex height width : Nat)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    pivotMagnitudeWithin matrix pivotIndex ≤ smithMinorAbsSum matrix pivotIndex height width :=
  smithMinorEntryLeAbsSum matrix pivotIndex height width pivotIndex pivotIndex
    (Nat.le_refl pivotIndex)
    (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pRowLt)
    (Nat.le_refl pivotIndex)
    (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pColLt)

/-! ## Brick 2 — cross-clean maintenance: the K1 guard is a loop invariant -/

/-- **One Bezout-drop round re-establishes the clean cross** — the round's trailing letter is the shipped
`smithCascadeSweep` at its ACTUAL seed fuel `smithMinorAbsSum afterClear`, so its output cross is clear by
`smithCascadeSweepSeedReachesCrossClear`.  The staged matrices `afterFold`/`afterSign`/`afterClear` are the
round's own `let`s; each stays rectangular by `applyOperationsPreservesRectangular` (mirrors the K1 proof).
This is the MAINTENANCE half of fuel adequacy: the K1 clean-cross guard is re-established every round, hence
a LOOP INVARIANT — not a fresh per-round assumption. -/
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

/-! ## Brick 3 — content invariance: the Bezout position sweep preserves the sub-block gcd -/

/-- **The Bezout-drop round WORD is bounded below the pivot** — every letter (the found-row fold, the
sign-normalise, the single Bezout column op, and the trailing cascade) is at indices `≥ pivotIndex ≥ lo`.
The fold source `foundRow` and the column target `foundCol` are `≥ pivotIndex` (the caller threads the
`smithFindNonDividingInBlockSomeProperties` witnesses); the sign word by
`smithSignNormalizeOpsBoundedBelow`, the cascade by `smithCascadeSweepBoundedBelow`.  So
`minorGcdStableUnderBoundedWord` (r43) applies UNCHANGED to the Bezout word. -/
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

/-- **The Bezout position-sweep WORD is bounded below the pivot** — the `none`-branch standalone cascade,
and the `some`-branch round word `++` the recursion, are all at indices `≥ pivotIndex ≥ lo`.  Structural on
`fuel`.  The `some`-branch found position sits at `≥ pivotIndex` by
`smithFindNonDividingInBlockSomeProperties` (both coordinates), feeding the round-word boundedness. -/
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

/-- **The Bezout position sweep preserves the sub-block content** (r43 applied to the Bezout word) —
`minorGcdWithin` of the `[pivotIndex, ·)²` block is INVARIANT across the Bezout position repair.  The
boundedness (`smithBezoutRepairPositionSweepBoundedBelow` at `lo := pivotIndex`) feeds
`minorGcdStableUnderBoundedWord`.  So the gcd of the LANDED minor equals the gcd of the INPUT minor. -/
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

/-! ## Brick 4 — K2: the single-position landed characterization (hypothesis-bound on find-`none`) -/

/-- **The Bezout-driver localized keystone** — IF the Bezout position sweep's landed pivot has whole-block
find-`none` (the loop's OWN `none`-branch termination condition, on the LANDED state), THEN `|landed pivot|
= |gcd(INPUT minor)|`.  Route: the r45 bridge `smithFindNonDividingInBlockNoneIffDivisibleWithin` turns
find-`none` into the whole-block divisibility the r44 keystone `blockDivisibilityImpliesAbsEqMinorGcd`
consumes, giving `|landed| = |gcd(LANDED minor)|`; the r43-style content invariance
`smithBezoutRepairPositionSweepPreservesMinorGcd` rewrites the LANDED minor gcd to the INPUT minor gcd.
Hypothesis-bound on the OPERATIONAL find-`none` — EXACTLY the Bezout loop's landing test.  The Bezout-word
twin of the r45 `smithRepairInBlockLandedFindNoneAbsEqInputMinorGcd`. -/
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

/-! ## Brick 5 — the reduction port: the mandate from the two Phase-B invariants -/

/-- **The Bezout driver's applied output splits off the sign phase** — the Bezout-word twin of
`smithReduceCompleteApplied`.  `smithReduceCompleteBezout`'s certificate is `diagOps ++ repairOps ++
signOps`; applying it splits into the sign sweep over the Bezout repair output (`applyOperationsAppend`
twice). -/
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

/-- **`nonnegHolds` for the Bezout driver (Phase C)** — the diagonal of the full Bezout-driver output is
nonnegative at every window position.  The Bezout-word twin of `smithReduceCompleteDiagonalNonneg`: the
applied output splits off the sign phase (`smithReduceCompleteBezoutApplied`), whose input `afterRepair`
stays rectangular (`applyOperationsPreservesRectangular`); `signSweepDiagonalNonnegReached` delivers
nonnegativity.  Word-agnostic in the sign phase — no Bezout-specific invariant is needed. -/
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

/-- **The Bezout-driver mandate reduced to the two Phase-B invariants** — `SmithReduceCompleteBezout
DriverStatement` follows from just TWO invariant obligations on the Bezout repair output `afterRepair`:
window-diagonality at 0 and the full prefix chain.  Phase C (`nonnegHolds`) is discharged internally
(`smithReduceCompleteBezoutDiagonalNonneg`); the sign phase carries window-diagonality and the chain from
`afterRepair` to the full output (`smithSignSweepPreservesWindowDiagonal` / `smithSignSweepPreservesChain`
composed with `smithReduceCompleteBezoutApplied`).  The Bezout-word twin of
`smithReduceCompleteDriverOfRepairInvariants`.  The two survivors are the r49 arc (ARC-C, fed by the
per-position K2 `smithBezoutLandedFindNoneAbsEqInputMinorGcd` and the fuel-adequacy find-`none`). -/
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

/-! ## Brick 6 — the r49 gate + the fuel-adequacy residual (recorded, honestly UNINHABITED) -/

/-- **The r49 gate — the two Phase-B invariants over the Bezout repair output** (recorded, UNINHABITED).
The conjunction of `smithReduceCompleteBezoutDriverOfRepairInvariants`'s two hypotheses.  Once this is
inhabited the #2261 mandate fires by `smithReduceCompleteBezoutMandateReducesToInvariants`.  It decomposes
into the fuel-adequacy find-`none` (`SmithBezoutRepairPositionSweepReachesFindNoneStatement`), the
per-position K2 (`smithBezoutLandedFindNoneAbsEqInputMinorGcd`, r48-shipped), and the word-tied
multi-position chain assembly (ARC-C).  It is NEVER inhabited by a weakened variant. -/
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

/-- **The mandate reduces to the r49 gate** — the #2261 mandate `SmithReduceCompleteBezoutDriverStatement`
is inhabited AS SOON AS `SmithBezoutRepairInvariantsStatement` is.  This is the CRISP honest cut: r48
discharges the reduction port; the residual is exactly the two named invariants.  Consumes the two
conjuncts through `smithReduceCompleteBezoutDriverOfRepairInvariants`. -/
theorem smithReduceCompleteBezoutMandateReducesToInvariants
    (invariants : SmithBezoutRepairInvariantsStatement) :
    SmithReduceCompleteBezoutDriverStatement :=
  smithReduceCompleteBezoutDriverOfRepairInvariants invariants.1 invariants.2

/-- **The fuel-adequacy residual (recorded, UNINHABITED)** — the fueled Bezout position sweep at its
ACTUAL seed `smithMinorAbsSum` REACHES find-`none` on a rectangular, clean-cross state.  This is the (A)
arc: structural on the fuel with the K1 measure `pivotMagnitudeWithin` as the decreasing witness (bounded
by the seed via `pivotMagnitudeWithinLeMinorAbsSum`), threading the maintenance
(`smithBezoutRepairRoundAtFoundReEstablishesCrossClean`) so the clean-cross guard is a loop invariant.  It
stays UNINHABITED in r48 — the two genuinely-open sub-obligations are the positivity-maintenance (find-
`some` ⟹ positive pivot on the reachable class, α) and the trailing-cascade-preserves-`none` (β).  Once
inhabited, it feeds the per-position K2 `smithBezoutLandedFindNoneAbsEqInputMinorGcd` toward the r49 gate.
It is NEVER inhabited by a weakened variant. -/
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
