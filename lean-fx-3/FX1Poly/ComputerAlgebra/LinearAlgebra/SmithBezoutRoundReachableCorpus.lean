import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutRoundReachable

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithBezoutRoundReachableCorpus — the committed trajectory
    corpus + the no-regression suite for the Bezout-drop round (H2-SMITH r47, #2261)

## The census (graveyard law)

Per the CENSUS LAW, every seed is a NAMED `IntMatrix.mk` def and every landing is a machine-checked
`#eval` pin or `decide` theorem — no prose counts.  The corpus is split into the two classes the graveyard
law demands:

  * **CLEAN-cross reachable seeds** (the loop states K1 applies to): the r45 killers `bezoutKillerA`
    (`[[6,0,0],[0,0,10],[0,0,0]]`, off-cross `10`) and `bezoutKillerB` (`[[2,0,0],[0,0,3],[0,3,0]]`,
    anti-diagonal `3`), plus the multi-round diagonal seeds `bezoutSixTenFifteen`,
    `bezoutThirtyTwentyTwelve`, and `bezoutTwoThree`.  On every one, ONE Bezout-drop round STRICTLY lowers
    the pivot magnitude (`6->2`, `2->1`, `6->2`, `30->12`, `2->1`) — including `30->12` where `12 ∤ 30`
    (the `sdvd` shape is FALSE yet the plain strict `<` HOLDS, the exact K1 point).

  * **DIRTY-cross / zero-pivot refuters** (the r46 graveyard entries, UNREACHABLE loop states): on
    `bezoutDirtyRefuter` (`[[2,0],[4,3]]`) one Bezout-drop round RISES `2->3` — K1's `smithPivotCrossClean`
    guard EXCLUDES it (its cross is dirty), so K1 does NOT claim descent there; and on
    `bezoutZeroPivotSeed` (`[[0,0],[0,4]]`) it rises `0->4` off the measure floor — K1's positivity guard
    excludes it.  These pins are the HONESTY witnesses that K1 is a GUARDED, DIFFERENT proposition from the
    refuted UNGUARDED forall — never a revived graveyard measure.

## The no-regression suite (route-B law)

The Bezout-drop position SWEEP `smithBezoutRepairPositionSweep` lands `|pivot| = |minorGcd|` on EVERY seed
— IDENTICAL to the shipped r45 min-abs driver: killer A `-> 2 = gcd`, killer B `-> 1 = gcd`, the clean
diagonals `-> 1 / 2 / 1`, and even the dirty refuters `-> 1 / 4 = gcd` (the Bezout drop + cascade absorb
the transient dirty-fold rise).  Machine-checked `decide` theorems below — a behaviour regression would be
a compile error.

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`/`WellFounded.fix`.  ASCII identifiers.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutRoundReachableCorpus.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

set_option maxRecDepth 100000

/-! ## The CLEAN-cross reachable corpus (K1 applies) -/

/-- Killer A: pivot `6`, clean cross, interior off-cross `10` (`6 ∤ 10`). -/
def bezoutKillerA : IntMatrix := IntMatrix.mk [[6, 0, 0], [0, 0, 10], [0, 0, 0]]

/-- Killer B: pivot `2`, clean cross, anti-diagonal interior `3` (`2 ∤ 3`). -/
def bezoutKillerB : IntMatrix := IntMatrix.mk [[2, 0, 0], [0, 0, 3], [0, 3, 0]]

/-- Clean diagonal `diag(6, 10, 15)` — multi-round `6 -> 2 -> 1`. -/
def bezoutSixTenFifteen : IntMatrix := IntMatrix.mk [[6, 0, 0], [0, 10, 0], [0, 0, 15]]

/-- Clean diagonal `diag(30, 20, 12)` — one round `30 -> 12` (`12 ∤ 30`, `sdvd` FALSE, strict `<` TRUE). -/
def bezoutThirtyTwentyTwelve : IntMatrix := IntMatrix.mk [[30, 0, 0], [0, 20, 0], [0, 0, 12]]

/-- Clean diagonal `diag(2, 3)` — one round `2 -> 1`. -/
def bezoutTwoThree : IntMatrix := IntMatrix.mk [[2, 0], [0, 3]]

/-! ## The DIRTY-cross / zero-pivot refuters (K1's guards EXCLUDE them) -/

/-- The r46 dirty-column refuter `[[2,0],[4,3]]` — cross NOT clean (`entry(1,0) = 4`). -/
def bezoutDirtyRefuter : IntMatrix := IntMatrix.mk [[2, 0], [4, 3]]

/-- The r46 zero-pivot seed `[[0,0],[0,4]]` — pivot magnitude `0`. -/
def bezoutZeroPivotSeed : IntMatrix := IntMatrix.mk [[0, 0], [0, 4]]

/-! ## Census pins — the per-seed `(inputPivot, oneRound, fullSweep, minorGcd, crossClean)` tuples -/

/-! Clean seeds: one Bezout-drop round DESCENDS the pivot magnitude (`6->2`, `2->1`, `6->2`, `30->12`,
`2->1`), the full sweep lands `= minorGcd`, and the cross is clean (`true`). -/
#eval (pivotMagnitudeWithin bezoutKillerA 0,
  pivotMagnitudeWithin (smithBezoutRepairRound bezoutKillerA 0 3 3) 0,
  ((bezoutKillerA.applyOperations
    (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutKillerA 0 3 3) bezoutKillerA 0 3 3)).diagonalEntryAt 0).natAbs,
  (minorGcdWithin bezoutKillerA 0 3 3).natAbs, smithCrossIsClear bezoutKillerA 0 3 3)
#eval (pivotMagnitudeWithin bezoutKillerB 0,
  pivotMagnitudeWithin (smithBezoutRepairRound bezoutKillerB 0 3 3) 0,
  ((bezoutKillerB.applyOperations
    (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutKillerB 0 3 3) bezoutKillerB 0 3 3)).diagonalEntryAt 0).natAbs,
  (minorGcdWithin bezoutKillerB 0 3 3).natAbs, smithCrossIsClear bezoutKillerB 0 3 3)
#eval (pivotMagnitudeWithin bezoutSixTenFifteen 0,
  pivotMagnitudeWithin (smithBezoutRepairRound bezoutSixTenFifteen 0 3 3) 0,
  ((bezoutSixTenFifteen.applyOperations
    (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutSixTenFifteen 0 3 3) bezoutSixTenFifteen 0 3 3)).diagonalEntryAt 0).natAbs,
  (minorGcdWithin bezoutSixTenFifteen 0 3 3).natAbs, smithCrossIsClear bezoutSixTenFifteen 0 3 3)
#eval (pivotMagnitudeWithin bezoutThirtyTwentyTwelve 0,
  pivotMagnitudeWithin (smithBezoutRepairRound bezoutThirtyTwentyTwelve 0 3 3) 0,
  ((bezoutThirtyTwentyTwelve.applyOperations
    (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutThirtyTwentyTwelve 0 3 3) bezoutThirtyTwentyTwelve 0 3 3)).diagonalEntryAt 0).natAbs,
  (minorGcdWithin bezoutThirtyTwentyTwelve 0 3 3).natAbs, smithCrossIsClear bezoutThirtyTwentyTwelve 0 3 3)
#eval (pivotMagnitudeWithin bezoutTwoThree 0,
  pivotMagnitudeWithin (smithBezoutRepairRound bezoutTwoThree 0 2 2) 0,
  ((bezoutTwoThree.applyOperations
    (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutTwoThree 0 2 2) bezoutTwoThree 0 2 2)).diagonalEntryAt 0).natAbs,
  (minorGcdWithin bezoutTwoThree 0 2 2).natAbs, smithCrossIsClear bezoutTwoThree 0 2 2)

/-! Refuters: one Bezout-drop round RISES (`2->3` dirty, `0->4` zero-pivot) — K1's guards EXCLUDE them
(cross NOT clean / pivot `0`) — yet the full sweep STILL lands `= minorGcd` (`1`, `4`). -/
#eval (pivotMagnitudeWithin bezoutDirtyRefuter 0,
  pivotMagnitudeWithin (smithBezoutRepairRound bezoutDirtyRefuter 0 2 2) 0,
  ((bezoutDirtyRefuter.applyOperations
    (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutDirtyRefuter 0 2 2) bezoutDirtyRefuter 0 2 2)).diagonalEntryAt 0).natAbs,
  (minorGcdWithin bezoutDirtyRefuter 0 2 2).natAbs, smithCrossIsClear bezoutDirtyRefuter 0 2 2)
#eval (pivotMagnitudeWithin bezoutZeroPivotSeed 0,
  pivotMagnitudeWithin (smithBezoutRepairRound bezoutZeroPivotSeed 0 2 2) 0,
  ((bezoutZeroPivotSeed.applyOperations
    (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutZeroPivotSeed 0 2 2) bezoutZeroPivotSeed 0 2 2)).diagonalEntryAt 0).natAbs,
  (minorGcdWithin bezoutZeroPivotSeed 0 2 2).natAbs, smithCrossIsClear bezoutZeroPivotSeed 0 2 2)

/-! ## K1 FIRES — a concrete strict-descent theorem via `smithBezoutRoundStrictlyDescendsOnCleanCross` -/

theorem bezoutKillerAIsRectangular : bezoutKillerA.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- **K1 applied to killer A** — the Bezout-drop round strictly lowers the pivot magnitude `6 -> 2` on the
clean-cross reachable killer A, DISCHARGED by the general theorem `smithBezoutRoundStrictlyDescendsOn
CleanCross` (all five guards `decide`d), not by re-`decide`-ing the round.  A theorem application, not a
literal. -/
theorem bezoutRoundDescendsOnKillerA :
    pivotMagnitudeWithin (smithBezoutRepairRound bezoutKillerA 0 3 3) 0
      < pivotMagnitudeWithin bezoutKillerA 0 :=
  smithBezoutRoundStrictlyDescendsOnCleanCross bezoutKillerA 0 3 3 bezoutKillerAIsRectangular
    (by decide) (by decide) rfl (by decide) (by decide)

/-! ## The no-regression suite — the Bezout sweep lands `|pivot| = |minorGcd|` (IDENTICAL to r45) -/

/-- **No-regression, killer A** — the Bezout sweep lands `|pivot| = |minorGcd| = 2` (r45 killer A pin). -/
theorem bezoutSweepKillerALandsMinorGcd :
    ((bezoutKillerA.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutKillerA 0 3 3) bezoutKillerA 0 3 3)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin bezoutKillerA 0 3 3).natAbs := by decide

/-- **No-regression, killer B** — the Bezout sweep lands `|pivot| = |minorGcd| = 1` (r45 killer B pin). -/
theorem bezoutSweepKillerBLandsMinorGcd :
    ((bezoutKillerB.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutKillerB 0 3 3) bezoutKillerB 0 3 3)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin bezoutKillerB 0 3 3).natAbs := by decide

/-- **No-regression, `diag(6,10,15)`** — the Bezout sweep lands `|pivot| = |minorGcd| = 1`. -/
theorem bezoutSweepSixTenFifteenLandsMinorGcd :
    ((bezoutSixTenFifteen.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutSixTenFifteen 0 3 3) bezoutSixTenFifteen 0 3 3)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin bezoutSixTenFifteen 0 3 3).natAbs := by decide

/-- **No-regression, `diag(30,20,12)`** — the Bezout sweep lands `|pivot| = |minorGcd| = 2`. -/
theorem bezoutSweepThirtyTwentyTwelveLandsMinorGcd :
    ((bezoutThirtyTwentyTwelve.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutThirtyTwentyTwelve 0 3 3) bezoutThirtyTwentyTwelve 0 3 3)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin bezoutThirtyTwentyTwelve 0 3 3).natAbs := by decide

/-- **No-regression, `diag(2,3)`** — the Bezout sweep lands `|pivot| = |minorGcd| = 1`. -/
theorem bezoutSweepTwoThreeLandsMinorGcd :
    ((bezoutTwoThree.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutTwoThree 0 2 2) bezoutTwoThree 0 2 2)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin bezoutTwoThree 0 2 2).natAbs := by decide

/-- **No-regression, the dirty refuter** — the Bezout SWEEP lands `|pivot| = |minorGcd| = 1` even where the
single round rises `2->3` (the drop + cascade absorb the transient dirty-fold rise). -/
theorem bezoutSweepDirtyRefuterLandsMinorGcd :
    ((bezoutDirtyRefuter.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutDirtyRefuter 0 2 2) bezoutDirtyRefuter 0 2 2)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin bezoutDirtyRefuter 0 2 2).natAbs := by decide

/-- **No-regression, the zero-pivot seed** — the Bezout sweep lands `|pivot| = |minorGcd| = 4`. -/
theorem bezoutSweepZeroPivotSeedLandsMinorGcd :
    ((bezoutZeroPivotSeed.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum bezoutZeroPivotSeed 0 2 2) bezoutZeroPivotSeed 0 2 2)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin bezoutZeroPivotSeed 0 2 2).natAbs := by decide

/-! ## The guard-honesty pin — the single round RISES on the dirty refuter (K1 does NOT claim descent) -/

/-- **The single Bezout-drop round RISES `2 -> 3` on the dirty refuter** — the exact r46 behaviour on a
DIRTY cross.  K1's `smithPivotCrossClean` guard excludes this state, so K1 is not contradicted: the
guarded descent is a DIFFERENT proposition from the refuted UNGUARDED forall.  `decide`, zero axioms. -/
theorem bezoutRoundRisesOnDirtyRefuter :
    ¬ (pivotMagnitudeWithin (smithBezoutRepairRound bezoutDirtyRefuter 0 2 2) 0
        < pivotMagnitudeWithin bezoutDirtyRefuter 0) := by decide

/-- **The dirty refuter's cross is NOT clean** — the witness that K1's guard genuinely excludes it. -/
theorem bezoutDirtyRefuterCrossNotClean :
    smithCrossIsClear bezoutDirtyRefuter 0 2 2 = false := by decide

end FX1Poly.ComputerAlgebra
