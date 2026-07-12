import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorGcdReduction
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorTransportEquivalence
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithAcrossRoundsContentInvariant

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithSubBlockContentInvariantProof — the recorded
    across-rounds content carrier `SmithSubBlockContentStableAcrossRound`, PROVEN GENERALLY
    (H2-SMITH r43, #2261)

r42 RECORDED `SmithSubBlockContentStableAcrossRound` (`SmithAcrossRoundsContentInvariant`) as a `Prop`
and pinned it constant on the trajectory seeds by `decide`, leaving its general proof DEFERRED under the
banner "content-invariance's cascade half is the same gcd-computation core as the `K2` off-diagonal wall".
r43 REFUTES that banner and ships the general proof: sub-block content invariance is NOT the keystone.
It is pure unimodular **ideal-preservation**, strictly WEAKER than `|landed| = gcd(minor)`, and the repo
already ships BOTH transport directions.  This file assembles them.

## The load-bearing generalisation (the reusable core)

`minorGcdStableUnderBoundedWord` — for ANY certificate word `word` confined below the pivot
(`allOpsBoundedBelow pivotIndex word = true`) applied to a rectangular `matrix`, the `[pivotIndex, .)^2`
sub-block gcd is UNCHANGED.  This is Stanley SNF Thm 2.4 (k = 1): the first determinantal divisor
(= gcd of all entries of the window) is invariant under every unimodular row/column operation confined
to the window.  Two towers plus antisymmetry:

  * **forward** (`gcd(matrix) | gcd(out)`): `minorGcdWithinDividesWithin` gives `gcd(matrix)` divides
    the input sub-block; the shipped forward tower `applyOperationsPreservesEntriesDivisibleWithin`
    carries that across the confined word to the output sub-block; `minorGcdWithinGreatest` reads off
    `gcd(matrix) | gcd(out)`.
  * **backward** (`gcd(out) | gcd(matrix)`): the sweep is UNIMODULAR, so its `reverseOperationWord` is
    confined below the pivot exactly where the forward word is (`reverseOperationWordBoundedBelow`), and
    the fold round-trip (`applyOperationsReverseRoundTrip`, rectangular) gives
    `out.applyOperations (reverse word) = matrix`; the same forward tower over the reverse word carries
    `gcd(out)`'s divisibility straight onto the input sub-block; `minorGcdWithinGreatest` closes.
  * both gcds are NONNEGATIVE (`intGcd = Int.ofNat ...`), so mutual `dividesExactly` descends to mutual
    `NatDivides` on the magnitudes, `natDividesAntisymm` gives magnitude equality, and nonneg + equal
    magnitude gives the `Int` equality (`intEqOfNonnegOfNatAbsEq`).

## The main theorem

`smithSubBlockContentStableAcrossRoundHolds : SmithSubBlockContentStableAcrossRound` — the recorded r42
`Prop`, byte-for-byte, now inhabited GENERALLY.  One clearing round is DEFINITIONALLY two nested
`applyOperations`: the fold word `[addRowMultiple foundPos pivotIndex 1]` then the Euclid cascade word.
Both are confined below the pivot (the fold by `pivotIndex < foundPos` from
`smithFindNonDividingLaterDiagonalSomeInRange`; the cascade by `smithCascadeSweepBoundedBelow`), so the
core lemma applies to each nested word, and the two content-equalities compose.  The pivot-in-range
premises (`pivotIndex < height`, `pivotIndex < width`), absent from the recorded `Prop`, are recovered
from `find = some foundPos` via `smithFindSomeImpliesPivotInRange` (`Nat.lt_or_ge` split, the `none`-arm
refuted structurally through `natSubEqZeroOfLe`).

## What this does NOT do (mandate banner — the mandate does NOT fire)

`SmithReduceCompleteDriverStatement` (`SmithNormalForm`) stays UNINHABITED hypothesis-free.  Content
invariance does NOT inhabit it: the driver needs `|landed| = gcd(minor)` (the keystone
`SmithCascadeLandedPivotDividesMinor` / `LandedAbsEqMinorGcdReachable`), REFUTED as stated (r33,
`[[0,6,0],[0,0,10],[0,0,0]]` lands `6` vs gcd `2`) and OPEN only in the driver image.  The r33 refuter is
the decisive independence witness: content is invariant (`gcd 2 -> 2`) exactly where the keystone fails
(`landed 6 != gcd 2`), so the two are distinct statements.  The round-pair magnitude descent
`SmithRoundPairPivotMagnitudeDescends` stays keystone-gated (content invariance ALONE cannot yield
magnitude descent — the r33 contrast shows landed magnitude `6` above content `2`); its eventual proof
route composes this theorem with `landedMagnitudeEqMinorGcdOfKeystone` (`SmithMinorGcdReduction`, shipped,
keystone-conditional) — NOT proved here.  No flip is fabricated.

Raw Lean 4 + `Init`, STRUCTURAL only.  ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`; no `WellFounded.fix`.  No `decide` on driver expressions — the
main theorem is a symbolic structural assembly.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithSubBlockContentInvariantProof.lean` (fuel-based
`#assert_no_axioms` AND independent `#print axioms`). -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## N1 — the pivot-in-range premises recovered from `find = some` -/

/-- **A `some`-find forces the pivot strictly in range** — when the diagonal find-scan over the driver
window reports `some foundPos`, the pivot is below both dimensions.  Split on
`Nat.lt_or_ge (pivotIndex + 1) (Nat.min height width)`: the `lt` arm delivers `pivotIndex < Nat.min ..`,
transported to `< height` / `< width` by `natMinLeLeft` / `natMinLeRight`; the `ge` arm makes the scan
count `Nat.min height width - (pivotIndex + 1)` collapse to `0` (`natSubEqZeroOfLe`), so the find-scan is
the `none` base — contradicting `= some foundPos` through `Option.noConfusion`.  Propext-clean: no
`Nat.sub_pos`/`Nat.not_le` (both leak); `Nat.lt_or_ge` and `natSubEqZeroOfLe` are structural. -/
theorem smithFindSomeImpliesPivotInRange (matrix : IntMatrix) (pivotIndex height width foundPos : Nat)
    (findEq : smithFindNonDividingLaterDiagonal matrix pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos) :
    pivotIndex < height ∧ pivotIndex < width := by
  cases Nat.lt_or_ge (pivotIndex + 1) (Nat.min height width) with
  | inl succLtMin =>
      have pivotLtMin : pivotIndex < Nat.min height width :=
        Nat.lt_of_le_of_lt (Nat.le_succ pivotIndex) succLtMin
      exact ⟨Nat.lt_of_lt_of_le pivotLtMin (natMinLeLeft height width),
        Nat.lt_of_lt_of_le pivotLtMin (natMinLeRight height width)⟩
  | inr minLeSucc =>
      have scanCountZero : Nat.min height width - (pivotIndex + 1) = 0 :=
        natSubEqZeroOfLe (Nat.min height width) (pivotIndex + 1) minLeSucc
      rw [scanCountZero] at findEq
      nomatch findEq

/-! ## N2 — the minor gcd is nonnegative -/

/-- **The rows gcd fold is nonnegative** — the empty fold is `0`; the successor fold is an `intGcd`, i.e.
an `Int.ofNat`.  Case split on the row count (no induction needed: each arm is directly nonnegative). -/
theorem minorGcdRowsNonneg (matrix : IntMatrix) (colStart colCount : Nat) :
    ∀ (rowCount rowStart : Nat), (0 : Int) ≤ minorGcdRows matrix colStart colCount rowCount rowStart
  | 0, _ => intZeroLeOfNat 0
  | _ + 1, _ =>
      intGcdIsNonnegative (minorGcdRow matrix _ colCount colStart)
        (minorGcdRows matrix colStart colCount _ _)

/-- **The `[pivotIndex, .)^2` sub-block gcd is nonnegative** — it is the outer rows fold. -/
theorem minorGcdWithinNonneg (matrix : IntMatrix) (pivotIndex height width : Nat) :
    (0 : Int) ≤ minorGcdWithin matrix pivotIndex height width :=
  minorGcdRowsNonneg matrix pivotIndex (width - pivotIndex) (height - pivotIndex) pivotIndex

/-! ## N3 — nonneg `Int`s with equal magnitude are equal -/

/-- **Two nonnegative `Int`s of equal magnitude are equal** — each is its own `Int.ofNat` magnitude
(`intOfNatNatAbsOfNonNeg`), and the magnitudes agree.  The antisymmetry closer for the two gcds. -/
theorem intEqOfNonnegOfNatAbsEq {leftValue rightValue : Int}
    (leftNonneg : (0 : Int) ≤ leftValue) (rightNonneg : (0 : Int) ≤ rightValue)
    (absEq : leftValue.natAbs = rightValue.natAbs) : leftValue = rightValue :=
  (intOfNatNatAbsOfNonNeg leftNonneg).symm.trans
    ((congrArg Int.ofNat absEq).trans (intOfNatNatAbsOfNonNeg rightNonneg))

/-! ## THE CORE — sub-block content is invariant under any bounded-below word -/

/-- **Sub-block content invariance under a confined unimodular word** (the reusable core; Stanley SNF
Thm 2.4, k = 1).  For any word confined below `pivotIndex` applied to a rectangular `matrix`, the
`[pivotIndex, .)^2` sub-block gcd is unchanged.  Forward tower (`gcd(matrix) | gcd(out)`) + reverse
round-trip tower (`gcd(out) | gcd(matrix)`) + nonneg antisymmetry.  This does NOT mention the cascade
or the fold — it is pure ideal-preservation, so it is the genuine general fact the recorded `Prop`
needs, strictly weaker than the `|landed| = gcd` keystone. -/
theorem minorGcdStableUnderBoundedWord {height width pivotIndex : Nat}
    (word : List ElementaryOperation) (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (wordBounded : allOpsBoundedBelow pivotIndex word = true) :
    minorGcdWithin (matrix.applyOperations word) pivotIndex height width
      = minorGcdWithin matrix pivotIndex height width := by
  have outRect : (matrix.applyOperations word).IsRectangular height width :=
    applyOperationsPreservesRectangular word matrix isRect
  have forwardDivides : dividesExactly (minorGcdWithin matrix pivotIndex height width)
      (minorGcdWithin (matrix.applyOperations word) pivotIndex height width) :=
    minorGcdWithinGreatest (matrix.applyOperations word) pivotIndex height width
      (minorGcdWithin matrix pivotIndex height width)
      (applyOperationsPreservesEntriesDivisibleWithin word matrix wordBounded
        (minorGcdWithinDividesWithin matrix pivotIndex height width isRect))
  have reverseBounded : allOpsBoundedBelow pivotIndex (reverseOperationWord word) = true :=
    (reverseOperationWordBoundedBelow pivotIndex word).trans wordBounded
  have roundTrip : (matrix.applyOperations word).applyOperations (reverseOperationWord word) = matrix :=
    applyOperationsReverseRoundTrip word matrix isRect
  have backwardOnInput : MatrixEntriesDivisibleByWithin
      (minorGcdWithin (matrix.applyOperations word) pivotIndex height width) pivotIndex matrix := by
    have transported := applyOperationsPreservesEntriesDivisibleWithin (reverseOperationWord word)
      (matrix.applyOperations word) reverseBounded
      (minorGcdWithinDividesWithin (matrix.applyOperations word) pivotIndex height width outRect)
    rw [roundTrip] at transported
    exact transported
  have backwardDivides : dividesExactly
      (minorGcdWithin (matrix.applyOperations word) pivotIndex height width)
      (minorGcdWithin matrix pivotIndex height width) :=
    minorGcdWithinGreatest matrix pivotIndex height width
      (minorGcdWithin (matrix.applyOperations word) pivotIndex height width) backwardOnInput
  exact intEqOfNonnegOfNatAbsEq
    (minorGcdWithinNonneg (matrix.applyOperations word) pivotIndex height width)
    (minorGcdWithinNonneg matrix pivotIndex height width)
    (natDividesAntisymm (natDividesNatAbsOfIntDivides forwardDivides)
      (natDividesNatAbsOfIntDivides backwardDivides)).symm

/-! ## THE MAIN THEOREM — the recorded r42 carrier, proven generally -/

/-- **`SmithSubBlockContentStableAcrossRound` proven GENERALLY** (the recorded r42 `Prop`, byte-intact).
On every nonzero-pivot find-`some` fold, one clearing round leaves the `[pivotIndex, .)^2` sub-block gcd
unchanged.  One round is DEFINITIONALLY the fold word `[addRowMultiple foundPos pivotIndex 1]` then the
Euclid cascade word (`smithClearingFoldStep`); each is confined below the pivot, so the core lemma
`minorGcdStableUnderBoundedWord` applies to each nested word and the two content-equalities compose.
Zero-axiom, structural, `decide`-free. -/
theorem smithSubBlockContentStableAcrossRoundHolds : SmithSubBlockContentStableAcrossRound := by
  intro work foundPos pivotIndex height width isRect findEq
  obtain ⟨pivotRowInRange, pivotColInRange⟩ :=
    smithFindSomeImpliesPivotInRange work pivotIndex height width foundPos findEq
  have pivotBelowFound : pivotIndex < foundPos :=
    (smithFindNonDividingLaterDiagonalSomeInRange work pivotIndex height width foundPos
      pivotRowInRange pivotColInRange findEq).1
  have foldBounded : allOpsBoundedBelow pivotIndex
      [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1)]
        = true :=
    boolAndBothTrue (opBoundedBelowAddRow pivotIndex foundPos pivotIndex 1
      (Nat.le_of_lt pivotBelowFound) (Nat.le_refl pivotIndex)) rfl
  have foldContent :
      minorGcdWithin (work.applyOperations
          [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1)])
          pivotIndex height width
        = minorGcdWithin work pivotIndex height width :=
    minorGcdStableUnderBoundedWord _ work isRect foldBounded
  have afterFoldRect : (work.applyOperations
      [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1)]).IsRectangular
        height width :=
    applyOperationsPreservesRectangular _ work isRect
  have cascadeBounded : allOpsBoundedBelow pivotIndex
      (smithCascadeSweep
        (smithMinorAbsSum (work.applyOperations
          [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1)])
          pivotIndex height width)
        (work.applyOperations
          [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1)])
        pivotIndex height width) = true :=
    smithCascadeSweepBoundedBelow pivotIndex _ _ pivotIndex height width
      pivotRowInRange pivotColInRange (Nat.le_refl pivotIndex)
  exact (minorGcdStableUnderBoundedWord _ _ afterFoldRect cascadeBounded).trans foldContent

/-! ## THE r43 LEDGER (H2-SMITH r43, #2261) — the honest general proof

**What this ships (zero-axiom, additive; the r18-r42 world byte-intact).**  The recorded r42 carrier
`SmithSubBlockContentStableAcrossRound` is now inhabited GENERALLY by
`smithSubBlockContentStableAcrossRoundHolds` — the first honest general (not `decide`-pinned) theorem in
the across-rounds refounding.  The reusable core `minorGcdStableUnderBoundedWord` (any confined unimodular
word preserves the sub-block gcd) is the load-bearing generalisation: a two-tower ideal-preservation
assembly of the SHIPPED forward tower (`applyOperationsPreservesEntriesDivisibleWithin`) and reverse
round-trip (`applyOperationsReverseRoundTrip` + `reverseOperationWordBoundedBelow`), closed by nonneg gcd
antisymmetry.  Helpers `smithFindSomeImpliesPivotInRange` (N1), `minorGcdWithinNonneg` (N2),
`intEqOfNonnegOfNatAbsEq` (N3) are the small additive bridges.

**The r42 banner CORRECTED.**  r42's footer claimed content invariance "rests on the same gcd-computation
core as `K2`".  That is REFUTED: content invariance is pure ideal-preservation, strictly WEAKER than the
`|landed| = gcd` keystone, and holds even on the r33 keystone refuter `[[0,6,0],[0,0,10],[0,0,0]]` where
`|landed| != gcd`.

**The mandate does NOT fire.**  `SmithReduceCompleteDriverStatement` stays UNINHABITED hypothesis-free;
this theorem does NOT reduce it (the driver needs `|landed| = gcd(minor)`, refuted-in-general / open in
the driver image, untouched here).  `SmithRoundPairPivotMagnitudeDescends` stays keystone-gated — content
invariance ALONE cannot yield magnitude descent (the r33 contrast: content `2`, landed magnitude `6`); its
eventual proof composes this theorem with `landedMagnitudeEqMinorGcdOfKeystone` (shipped, keystone-
conditional).  `K2` (`SmithClearingOutputOffDiagonalDivides`) stands UNCHANGED.  No flip is fabricated. -/

end FX1Poly.ComputerAlgebra
