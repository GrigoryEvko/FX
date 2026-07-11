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

/-! ## PART A3 — THE INTERIOR FILL-IN INVARIANT (the crux; the cascade-computes-gcd wall)

Target: the landed pivot `g := M'.diagonalEntryAt p` divides every OFF-DIAGONAL interior cell
`M'.entryAt r c` for `r > p, c > p, r ≠ c` (`SubBlockOffDiagonalDivisibleFrom g (p+1) M'`).

**Per-phase invariant (made exact).**  Each cascade rotation emits, in order: the move-to-pivot swaps,
the sign-normalize negate, the column-below clears (`entry(i, j) += −q_i · entry(p, j)`, a combination of
the pivot ROW), and the row-right clears (`entry(i, j) += −q'_j · entry(i, p)`, a combination of the
pivot COLUMN).  So the fill-in of rotation `k` is a ℤ-combination of `d_k`-multiples ONLY IF
`d_k ∣ (pivot row) ∧ d_k ∣ (pivot col)`, where `d_k` is the pivot value at rotation `k`.

**The chain composition + why it is circular.**  The min-abs re-selection PARKS strictly-smaller
remainders, so the pivot value CHANGES across rotations and the final landed `g = d_n`.  Threading the
invariant against `g` needs the **Euclidean divisibility chain** `g ∣ d_k` for every `k`.  Both halves
are circular against the target:
  * the per-phase premise `d_k ∣ pivot-row/col` is FALSE mid-rotation (that is exactly why the cascade
    LOOPS — `intPivotQuotient` is a MAGNITUDE quotient parking a nonzero remainder, not an exact
    divisor);
  * the chain `g ∣ d_k` needs `g = gcd(minor)`, which needs `g ∣` the whole minor — the target itself.

The ONLY non-circular divisor for which the shipped forward tower proves "d ∣ interior of `M'`" is a `d`
known a priori to divide the INPUT minor — instantiating `d := g` IS the keystone.  The
`InteriorDivByPhasePivot`/Euclidean-chain hope is genuinely NOT a loop invariant: the interior
ACCUMULATES across passes and is never overwritten (NODE E's
`smithClearingSweepInteriorNotDiagonalWitness`, `diag(15, 10, 6, 4)` interior `(3, 1) = −20`).  **A3 =
the seed's off-diagonal half = the cascade-computes-gcd / gcd-ideal-invariance major arc — the r11+ wall.
It is walled; it is not a loop invariant.**

**Probe-first (`diag(6, 10, 8)`).**  The pivot-0 sweep lands `g = 2 = gcd(6, 10, 8)` and the exit
interior is `diag(2, 30, 8)` — the interior entries `30, 8` are BOTH even (`2`-divisible), exactly the A3
content, exhibited on a gcd > 1 window.  The evenness holds ONLY because `2` is the minor gcd. -/

set_option maxRecDepth 8000 in
/-- **The exit interior is `2`-divisible on a concrete gcd > 1 window** — the pivot-0 clearing sweep of
`diag(6, 10, 8)` lands `2` at the pivot (`= gcd(6, 10, 8)`) and the exit interior diagonal entries
`30, 8` are BOTH `2`-divisible.  A machine-checked instance of the A3 content: the landed pivot divides
the interior fill-in, WITH concrete `dividesExactly` witnesses (`30 = 2·15`, `8 = 2·4`).  This is the
canonical case where A3 bites — the interior is even ONLY because `2` is the gcd. -/
theorem smithClearingSweepExitInteriorEvenOnConcreteWindow :
    (smithPivotClearingOutput { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0 3 3).diagonalEntryAt 0 = 2
      ∧ dividesExactly 2
          ((smithPivotClearingOutput { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0 3 3).entryAt 1 1)
      ∧ dividesExactly 2
          ((smithPivotClearingOutput { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0 3 3).entryAt 2 2) :=
  ⟨by decide, ⟨15, by decide⟩, ⟨4, by decide⟩⟩

/-! ## THE ASSEMBLY — the exit-divides ⟺ input-divides equivalence + the driver reduction (H2-SMITH B4)

The r22 residual `SmithCascadeLandedPivotDividesMinor` reads the landed pivot dividing the INPUT minor.
`SmithCascadeOutputMinorDivides` reads the SAME landed pivot dividing the OUTPUT `M'` minor.  Part B's
fold round-trip proves the two are **equivalent** (NOT sharper): because the sweep is unimodular, its
`reverseOperationWord` transports minor-divisibility across the confined word in BOTH directions —
forward tower (input ⟹ output), and Part-B round-trip (output ⟹ input).  So the honest r23 headline is
`keystone ⟺ SmithCascadeOutputMinorDivides`: one object, two presentations. -/

/-- **The output-side re-presentation of the residual** — the landed pivot `M'.diagonalEntryAt p`
divides every entry of the OUTPUT `M'`'s `[p, ·) × [p, ·)` minor (`M'` = the pivot-`p` clearing sweep
output).  Spelled out (not via `smithPivotClearingOutput`) so it matches the residual verbatim modulo the
sweep-output substitution in the target slot. -/
def SmithCascadeOutputMinorDivides : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    MatrixEntriesDivisibleByWithin
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      pivotIndex
      (matrix.applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width))

/-- **OUTPUT minor divides ⟹ INPUT minor divides (the inverse-transport half).**  Given the landed pivot
divides the OUTPUT `M'` minor, it divides the INPUT minor: the sweep `S` is confined below `p`
(`smithRepairPositionSweepClearingBoundedBelow`), so its `reverseOperationWord` is too
(`reverseOperationWordBoundedBelow`); the fold round-trip (`applyOperationsReverseRoundTrip`, rectangular)
gives `matrix = M'.applyOperations (reverseOperationWord S)`; the SHIPPED forward tower carries the
landed pivot's divisibility across that confined reverse word, landing on the INPUT minor.  The Part-B
payoff — no A1/A2/A3 needed for THIS direction. -/
theorem keystoneOfOutputMinorDivides (outputDivides : SmithCascadeOutputMinorDivides) :
    SmithCascadeLandedPivotDividesMinor := by
  intro matrix pivotIndex height width isRect pRowLt pColLt
  have roundTrip := applyOperationsReverseRoundTrip
    (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
      matrix pivotIndex height width) matrix isRect
  have reverseBounded : allOpsBoundedBelow pivotIndex
      (reverseOperationWord (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
        matrix pivotIndex height width)) = true :=
    (reverseOperationWordBoundedBelow pivotIndex _).trans
      (smithRepairPositionSweepClearingBoundedBelow pivotIndex
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
        pRowLt pColLt (Nat.le_refl pivotIndex))
  have transported := applyOperationsPreservesEntriesDivisibleWithin
    (reverseOperationWord (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
      matrix pivotIndex height width))
    (matrix.applyOperations (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
      matrix pivotIndex height width))
    reverseBounded (outputDivides matrix pivotIndex height width isRect pRowLt pColLt)
  rw [roundTrip] at transported
  exact transported

/-- **INPUT minor divides ⟹ OUTPUT minor divides (the forward-tower half, r22).**  The mirror direction:
the sweep is confined below `p`, so the SHIPPED forward tower carries the landed pivot's divisibility from
the INPUT minor straight to the OUTPUT `M'` minor. -/
theorem outputDividesOfKeystone (landedDivides : SmithCascadeLandedPivotDividesMinor) :
    SmithCascadeOutputMinorDivides := by
  intro matrix pivotIndex height width isRect pRowLt pColLt
  exact applyOperationsPreservesEntriesDivisibleWithin
    (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
      matrix pivotIndex height width) matrix
    (smithRepairPositionSweepClearingBoundedBelow pivotIndex
      (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
      pRowLt pColLt (Nat.le_refl pivotIndex))
    (landedDivides matrix pivotIndex height width isRect pRowLt pColLt)

/-- **THE EQUIVALENCE** — the input-side residual and the output-side re-presentation are the SAME object.
The honest r23 headline: Part B does NOT sharpen the residual; it proves the two presentations are
machine-checked equivalent (input-side and output-side of the unimodular sweep). -/
theorem outputMinorDividesIffLandedPivotDividesMinor :
    SmithCascadeOutputMinorDivides ↔ SmithCascadeLandedPivotDividesMinor :=
  ⟨keystoneOfOutputMinorDivides, outputDividesOfKeystone⟩

/-- **The corrected-driver totality from the output-side residual.**  Compose the inverse-transport half
with the shipped `smithReduceCompleteDriverOfLandedPivotDividesMinor`: `SmithReduceCompleteDriverStatement`
is inhabited GIVEN the output-side residual `SmithCascadeOutputMinorDivides` — equivalent to the r22
input-side residual, so the surviving obligation count is honestly still ONE. -/
theorem smithReduceCompleteDriverOfOutputMinorDivides (outputDivides : SmithCascadeOutputMinorDivides) :
    SmithReduceCompleteDriverStatement :=
  smithReduceCompleteDriverOfLandedPivotDividesMinor (keystoneOfOutputMinorDivides outputDivides)

/-- **The shipped ℤ-equivalence witness fires on the battery hostiles.**  `applyOperationsReverseRoundTrip`
(Part B) applied to the recon self-attack battery — the zero-pivot bootstrap `diag(0, 4)` (lands `4`), the
negative-entry window `[[6, −4], [0, 0]]` (lands `gcd 2`), and the coprime `diag(15, 10, 6, 4)` (lands `1`,
the NODE-E refuter of the r21 folded-pair name) — each round-trips exactly: the sweep is genuinely
invertible, so the reduced matrix is ℤ-equivalent to the input on every hostile. -/
theorem smithSweepRoundTripsOnBatteryHostiles :
    (({ rows := [[0, 0], [0, 4]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum { rows := [[0, 0], [0, 4]] } 0 2 2)
          { rows := [[0, 0], [0, 4]] } 0 2 2)).applyOperations
        (reverseOperationWord (smithRepairPositionSweepClearing (smithMinorAbsSum { rows := [[0, 0], [0, 4]] } 0 2 2)
          { rows := [[0, 0], [0, 4]] } 0 2 2))
      = { rows := [[0, 0], [0, 4]] }
    ∧ (({ rows := [[6, -4], [0, 0]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum { rows := [[6, -4], [0, 0]] } 0 2 2)
          { rows := [[6, -4], [0, 0]] } 0 2 2)).applyOperations
        (reverseOperationWord (smithRepairPositionSweepClearing (smithMinorAbsSum { rows := [[6, -4], [0, 0]] } 0 2 2)
          { rows := [[6, -4], [0, 0]] } 0 2 2))
      = { rows := [[6, -4], [0, 0]] }
    ∧ (({ rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4)
          { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4)).applyOperations
        (reverseOperationWord (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4)
          { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4))
      = { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } :=
  ⟨applyOperationsReverseRoundTrip _ _
      (⟨rfl, rfl, rfl, trivial⟩ : ({ rows := [[0, 0], [0, 4]] } : IntMatrix).IsRectangular 2 2),
   applyOperationsReverseRoundTrip _ _
      (⟨rfl, rfl, rfl, trivial⟩ : ({ rows := [[6, -4], [0, 0]] } : IntMatrix).IsRectangular 2 2),
   applyOperationsReverseRoundTrip _ _
      (⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ :
        ({ rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } : IntMatrix).IsRectangular 4 4)⟩

/-! ## THE MANDATE LEDGER (H2-SMITH B4, #2261) — the honest pair finalized; the surviving component named

**The user close criterion, quoted VERBATIM.**  "every rectangular integer matrix, any size, zero kernel
evaluation; the honest pair finalized" — i.e. `SmithReduceCompleteDriverStatement` inhabited
HYPOTHESIS-FREE.  This is **NOT reached** in r23.

**What r23 DELIVERS.**
  * Part B in full — the operation-inversion kit `applyOperationsReverseRoundTrip` (the ℤ-equivalence
    witness `A = M'.applyOperations (reverseOperationWord S)` the certificate design promised, discharging
    the ~20-round-old r2 residual) + the B2 transport-fit `reverseOperationWordBoundedBelow`, all
    zero-axiom, purely structural (no `decide`, ceiling-free).
  * `keystoneOfOutputMinorDivides` (pure inverse transport, no A1/A2/A3) + the forward-tower converse
    `outputDividesOfKeystone` + the machine-checked equivalence
    `outputMinorDividesIffLandedPivotDividesMinor : SmithCascadeOutputMinorDivides ↔
    SmithCascadeLandedPivotDividesMinor`.
  * `smithReduceCompleteDriverOfOutputMinorDivides : SmithCascadeOutputMinorDivides →
    SmithReduceCompleteDriverStatement`, composing the inverse transport with the r22 driver reduction.

**THE ONE SURVIVING COMPONENT, named EXACTLY.**  `SmithReduceCompleteDriverStatement` is inhabited GIVEN
`SmithCascadeLandedPivotDividesMinor` (⟺ `SmithCascadeOutputMinorDivides`) — the SINGLE surviving
obligation:

    the pivot-`p` clearing position sweep lands, at the pivot, a divisor of every entry of the input's
    (equivalently the output's) `[p, ·)` minor — its magnitude equals the minor gcd.

This is the "min-abs Euclid cascade computes the gcd" correctness — the r11+ wall, a STANDALONE MAJOR ARC.
Its three would-be shortcuts A1/A2/A3 are each adjudicated walled (A1/A2 = C3 fuel-adequacy; A3 = the
gcd-ideal invariance whose per-phase invariant + Euclidean chain is circular against the target).  The
residual is TRUE (probe-verified: `diag(6, 10, 8)` lands `2 = gcd`, interior `30, 8` even; the battery
hostiles round-trip and land their predicted pivots `4 / 2 / 1`), just not proven in general.

**Honest verdict.**  r23 does NOT close the driver hypothesis-free — the cascade-computes-gcd keystone
stays open.  It DOES: (B1) ship the full inverse round-trip kit, discharging the r2 ℤ-equivalence debt;
(B2/B3) adjudicate A1/A2/A3 each explicitly walled with concrete gcd > 1 truth-probes; (B4) prove the
input-side and output-side residuals machine-checked EQUIVALENT (not sharper) and wire the driver
reduction onto either presentation.  No flip is fabricated; the honest pair is
`(SmithReduceCompleteDriverStatement ⟸ SmithCascadeOutputMinorDivides` (⟺ the r22 keystone)`,
that keystone OPEN)`.  The r18–r22 world stays byte-intact (additive only). -/

end FX1Poly.ComputerAlgebra
