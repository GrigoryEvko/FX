import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableImageSeedFixtures

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithReachableImageSeedRestriction — the reachable-image
    seed restriction: retire the UNRESTRICTED seed hypothesis, exclude the refuter (H2-SMITH r35, #2261)

## The move

The corrected total driver `smithReduceComplete` reduces (r20) to a single per-pivot ESTABLISH seed
`SmithCascadeLandsDivisibleSubBlock` (`SmithWindowedChainReduction`).  That UNRESTRICTED `∀`-seed is
REFUTED (`smithCascadeLandsDivisibleSubBlockIsRefuted`, `SmithLandedMagnitudeRefuted`) on the
out-of-image matrix `[[0, 6, 0], [0, 0, 10], [0, 0, 0]]` — a matrix that is NOT window-diagonal and
that the driver's own carrier never threads.  r34 machine-checked (POSITIVE) that the seed's magnitude
body holds on the ACTUAL non-diagonal advanced matrices the carrier feeds; this module makes the next
structural move: it RE-PARAMETERIZES the carrier off a RESTRICTED seed that only quantifies over the
matrices actually reachable from the Phase-A output, and PROVES the refuter is excluded.

## What this module ships (positive, additive, zero-axiom)

  * **`ReachableFromPhaseA`** — an inductive trajectory predicate on `(IntMatrix, Nat)`: `base` is the
    Phase-A output at pivot `0` (matching `repairChainHoldsOfSeed`'s driver-start matrix byte-for-byte),
    `step` is one pivot-repair advance (matching the carrier's `ih` advance byte-for-byte).  The carrier
    NEVER eliminates a reachability witness — it only constructs and passes one — so no recursor fires
    in the hot path.

  * **`SmithCascadeLandsDivisibleSubBlockReachable`** — the restricted seed: the UNRESTRICTED seed body,
    guarded by `ReachableFromPhaseA height width matrix pivotIndex`.

  * **`chainWindowedThroughPivotsReachable`** / **`repairChainHoldsOfSeedReachable`** /
    **`smithReduceCompleteDriverOfSubBlockSeedReachable`** — the PARALLEL sibling chain of NODE A / NODE B
    / the driver collapse (`SmithWindowedChainReduction`, `:453` / `:541` / `:570`).  The 1238-line
    originals stay BYTE-INTACT; these are new declarations that thread the reachability witness by
    constructor application at every instantiation site (`ReachableFromPhaseA.base` at the driver start,
    `ReachableFromPhaseA.step` at each advance).  The driver collapse feeds the SHIPPED
    `smithReduceCompleteDriverOfChain`, which consumes ONLY the chain.

  * **`reachableAtZeroIsWindowDiagonal`** / **`refuterNotWindowDiagonal`** / **`refuterNotReachableAtZero`**
    — the refuter-exclusion adjudication.  Every matrix reachable at pivot `0` is window-diagonal (the
    Phase-A output is, `smithReduceTotalSweepDiagonalizes`); the refuter is NOT window-diagonal
    (`entryAt 0 1 = 6`); so the refuter is NOT reachable at pivot `0`.  The refutation certificate stays
    permanent and simply cannot supply `ReachableFromPhaseA 3 3 refuter 0` — the restriction is ALIVE,
    not dead.

## What this module does NOT claim (honesty banner)

This module inhabits NOTHING hypothesis-free.  `smithReduceCompleteDriverOfSubBlockSeedReachable` still
takes the RESTRICTED seed `SmithCascadeLandsDivisibleSubBlockReachable` as a hypothesis;
`SmithReduceCompleteDriverStatement` (`SmithNormalForm`) stays UNINHABITED with zero hypotheses; the
mandate does NOT fire.  The EXACT remaining hypothesis is `SmithCascadeLandsDivisibleSubBlockReachable`
— NOT refuted (the refuter is excluded, above), but NOT proven.  Its honest open content is the
restricted min-abs descent on the reachable set (`|landed| ≤ gcd`, the r11+ wall) plus the structural
invariant `reachablePivotCrossClearInteriorConfined` (the reachable pivot cross is clean and the only
off-diagonal content is confined to the strict `[p+1, ·)²` sub-block) — a standalone multi-round arc,
NOT r35-sized.  The r18–r34 world and `smithReduceComplete` stay byte-intact (additive only); no flip
is fabricated.

Raw Lean 4 + `Init`, STRUCTURAL only (fuel `Nat`).  ASCII identifiers; no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachableImageSeedRestriction.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The reachability predicate — the trajectory the driver's carrier actually visits -/

/-- **`ReachableFromPhaseA height width matrix pivotIndex`** — `matrix` at `pivotIndex` is reachable from
some rectangular input by the corrected driver's repair trajectory.  `base`: the Phase-A output at pivot
`0` (the byte-exact driver-start matrix of `repairChainHoldsOfSeed`, `:545`).  `step`: one pivot-repair
position-sweep advance (the byte-exact matrix the carrier's `ih` threads, `:521`).  Indexed on
`(IntMatrix, Nat)`; the recursive occurrence in `step` is strictly positive. -/
inductive ReachableFromPhaseA (height width : Nat) : IntMatrix → Nat → Prop
  | base (input : IntMatrix) (isRect : input.IsRectangular height width) :
      ReachableFromPhaseA height width
        (input.applyOperations (smithReduceTotal input height width).operations) 0
  | step (matrix : IntMatrix) (pivotIndex : Nat)
      (reached : ReachableFromPhaseA height width matrix pivotIndex) :
      ReachableFromPhaseA height width
        (matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width))
        (pivotIndex + 1)

/-! ## The restricted seed — the UNRESTRICTED body guarded by reachability -/

/-- **The reachable-image ESTABLISH seed.**  The verbatim body of the UNRESTRICTED
`SmithCascadeLandsDivisibleSubBlock` (`SmithWindowedDivisibility`, `:681`), quantified ONLY over the
matrices actually reachable from the Phase-A output.  The refuter `[[0, 6, 0], [0, 0, 10], [0, 0, 0]]`
cannot instantiate this seed — it is not reachable at pivot `0` (`refuterNotReachableAtZero`). -/
def SmithCascadeLandsDivisibleSubBlockReachable : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    ReachableFromPhaseA height width matrix pivotIndex →
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    MatrixEntriesDivisibleByWithin
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      (pivotIndex + 1)
      (matrix.applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width))

/-! ## NODE A sibling — the cross-pivot carrier, threading the reachability witness by construction

The PARALLEL of `chainWindowedThroughPivots` (`SmithWindowedChainReduction`, `:453`).  The 1238-line
original is untouched; this sibling adds a `ReachableFromPhaseA height width matrix pivotIndex`
hypothesis to the induction motive and discharges the seed's reachability side-condition at the
`earlier = pivotIndex` branch (passing the incoming witness) and the `ih` advance (passing
`ReachableFromPhaseA.step`).  The body is otherwise the byte-exact original. -/
theorem chainWindowedThroughPivotsReachable (seed : SmithCascadeLandsDivisibleSubBlockReachable) :
    ∀ (outerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      ReachableFromPhaseA height width matrix pivotIndex →
      MatrixDiagonalChainWindowed matrix pivotIndex →
      MatrixDiagonalChainWindowed
        (matrix.applyOperations (smithDivisibilityRepairSweepClearing outerFuel matrix pivotIndex height width))
        (Nat.min (Nat.min height width) (pivotIndex + outerFuel)) := by
  intro outerFuel
  induction outerFuel with
  | zero =>
      intro matrix pivotIndex height width _ _ chainHolds
      exact matrixDiagonalChainWindowedMonotone matrix pivotIndex _ chainHolds
        (natMinLeRight (Nat.min height width) (pivotIndex + 0))
  | succ outerFuel ih =>
      intro matrix pivotIndex height width isRect reached chainHolds
      rw [smithDivisibilityRepairSweepClearingSucc]
      split
      · rename_i guardTrue
        have pivotRowInRange : pivotIndex < height := Nat.le_trans guardTrue (natMinLeLeft height width)
        have pivotColInRange : pivotIndex < width := Nat.le_trans guardTrue (natMinLeRight height width)
        have afterPositionChain :
            MatrixDiagonalChainWindowed
              (matrix.applyOperations (smithRepairPositionSweepClearing
                (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
              (pivotIndex + 1) := by
          intro earlierIndex earlierLtSucc
          cases Nat.lt_or_ge earlierIndex pivotIndex with
          | inl earlierLtPivot =>
              have positionBounded :
                  allOpsBoundedBelow (earlierIndex + 1)
                    (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
                      matrix pivotIndex height width) = true :=
                allOpsBoundedBelowMonotone (earlierIndex + 1) pivotIndex earlierLtPivot _
                  (smithRepairPositionSweepClearingBoundedBelow pivotIndex
                    (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
                    pivotRowInRange pivotColInRange (Nat.le_refl pivotIndex))
              have transported :
                  MatrixEntriesDivisibleByWithin (matrix.diagonalEntryAt earlierIndex) (earlierIndex + 1)
                    (matrix.applyOperations (smithRepairPositionSweepClearing
                      (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width)) :=
                applyOperationsPreservesEntriesDivisibleWithin
                  (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
                    matrix pivotIndex height width)
                  matrix positionBounded (chainHolds earlierIndex earlierLtPivot)
              have divisorFrozen :
                  (matrix.applyOperations (smithRepairPositionSweepClearing
                      (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width)).diagonalEntryAt earlierIndex
                    = matrix.diagonalEntryAt earlierIndex :=
                applyOperationsFreezeEntryBelow
                  (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
                    matrix pivotIndex height width)
                  matrix earlierIndex earlierIndex
                  (smithRepairPositionSweepClearingFreezesBelow pivotIndex
                    (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
                    pivotRowInRange pivotColInRange (Nat.le_refl pivotIndex))
                  earlierLtPivot earlierLtPivot
              rw [divisorFrozen]
              exact transported
          | inr earlierGePivot =>
              have earlierEqPivot : earlierIndex = pivotIndex :=
                Nat.le_antisymm (Nat.le_of_lt_succ earlierLtSucc) earlierGePivot
              rw [earlierEqPivot]
              exact seed matrix pivotIndex height width reached isRect pivotRowInRange pivotColInRange
        have afterPositionRect :
            (matrix.applyOperations (smithRepairPositionSweepClearing
              (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width)).IsRectangular height width :=
          applyOperationsPreservesRectangular _ matrix isRect
        have ihResult := ih
          (matrix.applyOperations (smithRepairPositionSweepClearing
            (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
          (pivotIndex + 1) height width afterPositionRect
          (ReachableFromPhaseA.step matrix pivotIndex reached) afterPositionChain
        rw [Nat.succ_add pivotIndex outerFuel] at ihResult
        rw [applyOperationsAppend]
        exact ihResult
      · rename_i guardFalse
        have minLePivot : Nat.min height width ≤ pivotIndex :=
          Nat.le_of_lt_succ (Nat.not_le.1 guardFalse)
        exact matrixDiagonalChainWindowedMonotone matrix pivotIndex _ chainHolds
          (Nat.le_trans (natMinLeLeft (Nat.min height width) (pivotIndex + (outerFuel + 1))) minLePivot)

/-! ## NODE B sibling — the reduction: restricted seed ⟹ `repairChainHolds` -/

/-- **NODE B sibling — the restricted seed yields the corrected driver's `repairChainHolds`.**  The
PARALLEL of `repairChainHoldsOfSeed` (`:541`).  Instantiating the sibling carrier at the driver start
(`pivotIndex := 0`, `outerFuel := Nat.min height width`, matrix := Phase-A output), the base reachability
witness is `ReachableFromPhaseA.base matrix isRect`; the cap collapses (`Nat.zero_add` + `natMinSelf`) and
the SHIPPED read-off `smithChainPrefixOfDiagonalChainWindowed` yields the `SmithChainPrefix` conjunct. -/
theorem repairChainHoldsOfSeedReachable (seed : SmithCascadeLandsDivisibleSubBlockReachable) :
    ∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      SmithChainPrefix
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithDivisibilityRepairSweepClearing (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        (Nat.min height width) height width :=
  fun matrix height width isRect =>
    smithChainPrefixOfDiagonalChainWindowed
      ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
        (smithDivisibilityRepairSweepClearing (Nat.min height width)
          (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
      (Nat.min height width) height width
      (by
        have windowedAtCap :=
          chainWindowedThroughPivotsReachable seed (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations)
            0 height width
            (applyOperationsPreservesRectangular _ matrix isRect)
            (ReachableFromPhaseA.base matrix isRect)
            (fun earlierIndex earlierLtZero => absurd earlierLtZero (Nat.not_lt_zero earlierIndex))
        rw [Nat.zero_add, natMinSelf] at windowedAtCap
        exact windowedAtCap)

/-- **NODE B sibling — the corrected driver totality on the RESTRICTED seed ALONE.**  The PARALLEL of
`smithReduceCompleteDriverOfSubBlockSeed` (`:570`).  Feed the reduced chain into the SHIPPED
`smithReduceCompleteDriverOfChain` (which consumes ONLY the chain).  A pure structural assembly term (no
kernel evaluation — the defeq ceiling is untouched).  The remaining hypothesis is EXACTLY the restricted
seed `SmithCascadeLandsDivisibleSubBlockReachable`; the mandate does NOT fire hypothesis-free. -/
theorem smithReduceCompleteDriverOfSubBlockSeedReachable
    (seed : SmithCascadeLandsDivisibleSubBlockReachable) :
    SmithReduceCompleteDriverStatement :=
  smithReduceCompleteDriverOfChain (repairChainHoldsOfSeedReachable seed)

/-! ## Refuter exclusion — the restriction is ALIVE (the refuter is NOT reachable at pivot `0`) -/

/-- **Every matrix reachable at pivot `0` is window-diagonal.**  Case on the reachability witness: the
`step` constructor produces index `pivotIndex + 1 ≠ 0` (auto-discharged), leaving `base`, whose matrix is
the Phase-A output — window-diagonal by the SHIPPED `smithReduceTotalSweepDiagonalizes` (the
`(smithReduceTotal · ·).operations` projection is definitionally the total sweep). -/
theorem reachableAtZeroIsWindowDiagonal (height width : Nat) (matrix : IntMatrix)
    (reached : ReachableFromPhaseA height width matrix 0) :
    IsWindowDiagonal matrix 0 height width := by
  cases reached with
  | base input isRect =>
      intro rowIndex colIndex _ rowLt _ colLt rowNeCol
      exact smithReduceTotalSweepDiagonalizes input height width isRect
        rowIndex colIndex rowLt colLt rowNeCol

/-- **The refuter is NOT window-diagonal.**  `[[0, 6, 0], [0, 0, 10], [0, 0, 0]].entryAt 0 1 = 6 ≠ 0`,
in the `[0, ·)` window of the `3 × 3` frame. -/
theorem refuterNotWindowDiagonal :
    ¬ IsWindowDiagonal { rows := [[0, 6, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3 :=
  fun isDiag =>
    absurd (isDiag 0 1 (Nat.zero_le 0) (by decide) (Nat.zero_le 1) (by decide) (by decide)) (by decide)

/-- **THE REFUTER IS NOT REACHABLE AT PIVOT `0` — the restriction is ALIVE.**  Were the refuter reachable
at pivot `0`, it would be window-diagonal (`reachableAtZeroIsWindowDiagonal`); it is not
(`refuterNotWindowDiagonal`).  So the UNRESTRICTED refutation certificate
(`smithCascadeLandsDivisibleSubBlockIsRefuted`) cannot supply a witness for the RESTRICTED seed — the
restriction is not dead. -/
theorem refuterNotReachableAtZero :
    ¬ ReachableFromPhaseA 3 3 { rows := [[0, 6, 0], [0, 0, 10], [0, 0, 0]] } 0 :=
  fun reached => refuterNotWindowDiagonal (reachableAtZeroIsWindowDiagonal 3 3 _ reached)

/-! ## The r35 ledger (H2-SMITH r35, #2261) — the reachable-image restriction

**What r35 ships (all zero-axiom, additive; the r18–r34 world byte-intact).**  The inductive trajectory
predicate `ReachableFromPhaseA`; the restricted seed `SmithCascadeLandsDivisibleSubBlockReachable`; the
parallel sibling carrier / reduction / driver-collapse
(`chainWindowedThroughPivotsReachable`, `repairChainHoldsOfSeedReachable`,
`smithReduceCompleteDriverOfSubBlockSeedReachable`) that retire the UNRESTRICTED seed hypothesis by
threading a reachability witness by constructor application; and the refuter-exclusion adjudication
(`reachableAtZeroIsWindowDiagonal`, `refuterNotWindowDiagonal`, `refuterNotReachableAtZero`) proving the
r33 refuter is NOT reachable — the restriction is ALIVE.

**What r35 does NOT ship.**  No hypothesis-free inhabitant of `SmithReduceCompleteDriverStatement` — the
mandate does NOT fire.  `smithReduceCompleteDriverOfSubBlockSeedReachable` still consumes the RESTRICTED
seed `SmithCascadeLandsDivisibleSubBlockReachable`, the EXACT remaining hypothesis.  Its honest open
content — the (ii) residual — is the reachable-set min-abs descent `|landed| ≤ gcd` (the r11+ wall)
resting on the structural invariant `reachablePivotCrossClearInteriorConfined` (reachable states have a
clean pivot cross with off-diagonal content confined to the strict `[p+1, ·)²` sub-block, the exact
structural property the refuter violates via its dirty pivot row `entryAt 0 1 = 6`).  Each is a
standalone multi-round arc; neither is r35-sized.  No flip is fabricated. -/

end FX1Poly.ComputerAlgebra
