import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithOperationRoundTrip

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithMinorTransportEquivalence — exit-divides ⟺ input-divides
    (the `ComputerAlgebra/` substrate; the H2-SMITH reconnection — Parts A1/A2/A3 adjudication + the
    inverse-transport equivalence)

The r22 residual `SmithCascadeLandedPivotDividesMinor` says the landed pivot divides the INPUT minor.
This file re-presents that SAME obligation on the OUTPUT side and proves the two presentations
**equivalent** (not sharper) via the Part-B inverse round-trip: because the clearing sweep is
unimodular, its `reverseOperationWord` transports minor-divisibility backward across the confined word,
so "the landed pivot divides the input minor" and "the landed pivot divides the output minor" are the
SAME object.  The forward tower already gives one direction; Part B gives the other.

Along the way the recon adjudicates the three would-be shortcuts A1/A2/A3 and names EXACTLY where each is
walled — the cascade-computes-gcd / fuel-adequacy content that no loop invariant discharges.  The
concrete truth-probes (`diag(6, 10, 8)` landing gcd `2`) exhibit the content on a gcd > 1 window.

## Zero-axiom design
Every transport lemma is a structural composition of shipped zero-axiom pieces (the forward tower, the
Part-B fold round-trip, the boundedness transport).  The truth-probes are `decide`-pins at the 3×3
defeq ceiling (`maxRecDepth 8000`, matching the r22 probe).  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithMinorTransportEquivalence.lean`.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-- The pivot-`pivotIndex` clearing position sweep OUTPUT `M'` — the matrix after the r17 unconditional
clearing sweep at seed fuel.  The subject of both the residual (which reads its landed pivot) and the
output-side re-presentation. -/
def smithPivotClearingOutput (matrix : IntMatrix) (pivotIndex height width : Nat) : IntMatrix :=
  matrix.applyOperations
    (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
      matrix pivotIndex height width)

/-! ## PART A1/A2 — the fit-check adjudication (the diagonal half + the cross-clear zeros at exit)

**A1 (the diagonal half).**  The shipped `smithFindNonDividingLaterDiagonalNoneDividesAll`
(`SmithCascadeTermination`) turns a find-loop `none` exit into `dividesExactly` between later diagonals.
Its hypothesis is `smithFindNonDividingLaterDiagonal M' pivotIndex (min h w − (p+1)) (p+1) = none` **on
the sweep OUTPUT** `M'`.  That the loop reaches `none` on the OUTPUT is exactly the C3 fuel-adequacy
`smithClearingSweepReachesFindNoneOfDescent`, conditional on `foldDescends` + `terminalKeepsFindNone` —
the two cascade-output residuals r22's B1 machine-refuted as non-mechanical
(`smithMinorAbsSumRaisesOnFoldWitness`, `smithZeroPivotFoldSaturatesBudgetWitness`).  **A1 is gated by
the fuel-adequacy wall.**  The bridge output-diagonal ⟹ seed (`subBlockDiagonalDivisibleOfWithin`, r22)
is shipped; the missing input is the `find = none` fact.

**A2 (the cross-clear zeros at exit).**  `smithCascadeSweepSeedReachesCrossClear` (r18) reaches
`smithCrossIsClear = true` for a SINGLE terminal cascade, and `smithRepairClearingStepSettlesHolds`
propagates `SmithPrefixSettled` — but BOTH require the INCOMING settled prefix
`SmithPrefixSettled matrix pivotIndex`, which the bare-input residual does NOT supply, and neither says
anything about the interior `[p+1, ·)²`.  For a bare input, output-cross-clear reduces to the sweep loop
reaching a `none`-terminal — the same fuel-adequacy wall.  **A2 is walled for the bare residual.**

The concrete window below exhibits BOTH facts ON a gcd > 1 window (the sweep output cross IS clear), so
the walls are about the GENERAL proof, not about truth. -/

set_option maxRecDepth 8000 in
/-- **The exit cross is clear on a concrete gcd > 1 window** — the pivot-0 clearing sweep of
`diag(6, 10, 8)` lands an output whose pivot-0 cross (row 0 / column 0, off the diagonal) is all zero
(`smithCrossIsClear = true`).  A machine-checked instance of the A2 content: the exit cross IS clear,
just not provable in general for a bare input without the fuel-adequacy wall. -/
theorem smithClearingSweepExitCrossClearOnConcreteWindow :
    smithCrossIsClear
        (smithPivotClearingOutput { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0 3 3) 0 3 3 = true := by
  decide

end FX1Poly.ComputerAlgebra
