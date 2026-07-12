import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractorKit

/-! # Polygraph/Omega/WalkingBunchedBimonoidPermMatrixExtractorGates — the matrix-algebra gates (a)/(b) that
close the GENERIC permutation-matrix extractor (WP-PROP r13, #2033)

★ **THE r13 GATES — the entry-wise `directSum`-quadrant match (gate (a)) + the finite-sum indicator-picks-one
column-swap law (gate (b)) + the extractor induction (K1).**  The r11 `WalkingBunchedBimonoidPermMatrixExtractor`
walled the GENERIC extractor `evalCell (permWord w width) = permMatrixOf width (permOfWord w width)` on exactly
three lemmas named in `fxBunchedBimonoid_genericPermMatrixExtractorGatedOnMatrixAlgebraKit`; the r12 Kit shipped
the shared relabel keystone (RELABEL-GET), gate (c), and gate (a)'s closed block-form
(`bunchedBimonoidSigmaAtBlockForm`).  This file discharges the two matrix-algebra gates and assembles K1:

  * **The well-formedness kit** — `bunchedBimonoidRangeMapMatWellFormed` (any `List.range`-double-map matrix is
    well-formed) instantiated at `identityMat` / `permMatrixOf` / `matMul`, plus `directSum` well-formedness and
    the `sigma2x2` singleton; the `bunchedBimonoidMatWellFormed` hypotheses the quadrant reads / reconstruction
    demand, all unconditionally dischargeable.
  * **`bunchedBimonoidMatExtByEntries`** — matrix extensionality by `matEntryAt` (via the shipped
    `bunchedBimonoidMatReconstruct` + `bunchedBimonoidMatEqOfEntries`; no new `List (List Nat)` extensionality).
  * **GATE (a)** `bunchedBimonoidSigmaAtIsTransposition` — `evalCell (sigmaAt width k) = permMatrixOf width
    (applyAdjacentSwap (range width) k)` for `k + 2 <= width`, via the block-form + a 4x4 index-region case split
    over the `directSum` quadrant reads + RELABEL-GET.
  * **GATE (b)** `bunchedBimonoidMatMulColumnSwapLaw` — `matMul (permMatrixOf p) (permMatrixOf (swap range k))
    = permMatrixOf (p.map (swapValue k))` for valid `k`, bounded `p`, via `matMulEntryRead` + the delta collapse.
  * **`bunchedBimonoidPermMatrixOfRangeIsIdentity`** + **`bunchedBimonoidPermOfWordEntriesBelow`** — the K1 base
    and the boundedness side-lemma.
  * **K1** `bunchedBimonoidPermWordExtractor` — the generic extractor, structural on the word.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin.  Mirror of the Brauer canonicity lane; never imported from it. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The width->=4 permutation-matrix reductions the pins exercise exceed the default heartbeat budget; the raise is
a compute allowance only, the proof terms stay axiom-free (uniform with the r6-r12 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # W — THE WELL-FORMEDNESS KIT (every shipped matrix is well-formed, unconditionally)
    # =========================================================================================
-/

/-- **List-append length** `(left ++ right).length = left.length + right.length` — hand-rolled (Init's
`List.length_append` routes through `simp`).  Structural on the first list; the successor step closes by
`Nat.succ_add`.  Propext-clean. -/
theorem bunchedBimonoidListLengthAppend {carrier : Type _} :
    ∀ (left right : List carrier), (left ++ right).length = left.length + right.length
  | [], right => (Nat.zero_add right.length).symm
  | _ :: tail, right => by
      show (tail ++ right).length + 1 = (tail.length + 1) + right.length
      rw [Nat.succ_add, bunchedBimonoidListLengthAppend tail right]

/-- ★ **Any `List.range`-double-map matrix is well-formed.**  A matrix whose `entries` are `(range rows).map
(fun i => (range cols).map (fun j => entryFn i j))` has the well-formedness invariant: the row count is `rows`
(map / range length), and every in-range row has length `cols`.  The reusable well-formedness backbone for
`identityMat` / `permMatrixOf` / `matMul` — all built from this shape. -/
theorem bunchedBimonoidRangeMapMatWellFormed (rowCount colCount : Nat) (entryFn : Nat → Nat → Nat) :
    bunchedBimonoidMatWellFormed
      { rows := rowCount, cols := colCount,
        entries := (List.range rowCount).map (fun rowIndex =>
          (List.range colCount).map (fun colIndex => entryFn rowIndex colIndex)) } := by
  refine ⟨?_, ?_⟩
  · show ((List.range rowCount).map (fun rowIndex =>
        (List.range colCount).map (fun colIndex => entryFn rowIndex colIndex))).length = rowCount
    rw [bunchedBimonoidListMapLength, bunchedBimonoidRangeLength]
  · intro rowIndex rowBelow
    show (bunchedBimonoidRowListGet ((List.range rowCount).map (fun rowIndexInner =>
        (List.range colCount).map (fun colIndex => entryFn rowIndexInner colIndex))) rowIndex).length = colCount
    rw [bunchedBimonoidRowListGetRangeMap rowCount
        (fun rowIndexInner => (List.range colCount).map (fun colIndex => entryFn rowIndexInner colIndex))
        rowIndex rowBelow,
      bunchedBimonoidListMapLength, bunchedBimonoidRangeLength]

/-- The identity matrix is well-formed. -/
theorem bunchedBimonoidIdentityMatWellFormed (dimension : Nat) :
    bunchedBimonoidMatWellFormed (bunchedBimonoidIdentityMat dimension) :=
  bunchedBimonoidRangeMapMatWellFormed dimension dimension (fun rowIndex colIndex => if rowIndex == colIndex then 1 else 0)

/-- The permutation matrix is well-formed. -/
theorem bunchedBimonoidPermMatrixWellFormed (width : Nat) (perm : List Nat) :
    bunchedBimonoidMatWellFormed (bunchedBimonoidPermMatrixOf width perm) :=
  bunchedBimonoidRangeMapMatWellFormed width width
    (fun rowIndex colIndex => if bunchedBimonoidNatListGet perm rowIndex == colIndex then 1 else 0)

/-- The matrix product is well-formed. -/
theorem bunchedBimonoidMatMulWellFormed (later earlier : BunchedBimonoidMat) :
    bunchedBimonoidMatWellFormed (bunchedBimonoidMatMul later earlier) :=
  bunchedBimonoidRangeMapMatWellFormed later.rows earlier.cols
    (fun rowIndex colIndex =>
      bunchedBimonoidNatListSum ((List.range earlier.rows).map (fun contractionIndex =>
        bunchedBimonoidMatEntryAt later rowIndex contractionIndex
          * bunchedBimonoidMatEntryAt earlier contractionIndex colIndex)))

/-- The `2 x 2` swap generator matrix `[[0,1],[1,0]]` is well-formed. -/
theorem bunchedBimonoidSigma2x2WellFormed :
    bunchedBimonoidMatWellFormed { rows := 2, cols := 2, entries := [[0, 1], [1, 0]] } :=
  ⟨rfl, fun rowIndex rowBelow => by
    match rowIndex with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ rowBelow)) (Nat.not_lt_zero _)⟩

/-- ★ **`directSum` preserves well-formedness.**  With both blocks well-formed, `directSum topBlock bottomBlock`
is well-formed: the row count is `topBlock.rows + bottomBlock.rows` (append / map length), and each row — top
(padded on the right) or bottom (padded on the left) — has length `topBlock.cols + bottomBlock.cols`. -/
theorem bunchedBimonoidDirectSumWellFormed (topBlock bottomBlock : BunchedBimonoidMat)
    (wfTop : bunchedBimonoidMatWellFormed topBlock) (wfBottom : bunchedBimonoidMatWellFormed bottomBlock) :
    bunchedBimonoidMatWellFormed (bunchedBimonoidMatDirectSum topBlock bottomBlock) := by
  have mappedTopLen : (topBlock.entries.map (fun row => row ++ List.replicate bottomBlock.cols 0)).length
      = topBlock.rows := by rw [bunchedBimonoidListMapLength]; exact wfTop.1
  refine ⟨?_, ?_⟩
  · show ((topBlock.entries.map (fun row => row ++ List.replicate bottomBlock.cols 0)) ++
        (bottomBlock.entries.map (fun row => List.replicate topBlock.cols 0 ++ row))).length
      = topBlock.rows + bottomBlock.rows
    rw [bunchedBimonoidListLengthAppend, mappedTopLen, bunchedBimonoidListMapLength, wfBottom.1]
  · intro rowIndex rowBelow
    show (bunchedBimonoidRowListGet
        ((topBlock.entries.map (fun row => row ++ List.replicate bottomBlock.cols 0)) ++
          (bottomBlock.entries.map (fun row => List.replicate topBlock.cols 0 ++ row))) rowIndex).length
      = topBlock.cols + bottomBlock.cols
    rcases Nat.lt_or_ge rowIndex topBlock.rows with rowLow | rowHigh
    · rw [bunchedBimonoidRowListGetAppendLow _ _ rowIndex (by rw [mappedTopLen]; exact rowLow),
        bunchedBimonoidRowListGetMap (fun row => row ++ List.replicate bottomBlock.cols 0) topBlock.entries
          rowIndex (by rw [wfTop.1]; exact rowLow),
        bunchedBimonoidListLengthAppend, wfTop.2 rowIndex rowLow,
        bunchedBimonoidListLengthReplicate]
    · have shiftedInRange : rowIndex - topBlock.rows < bottomBlock.entries.length := by
        rw [wfBottom.1]; exact bunchedBimonoidSubLtOfLtAdd rowHigh rowBelow
      rw [bunchedBimonoidRowListGetAppendHigh _ _ rowIndex (by rw [mappedTopLen]; exact rowHigh), mappedTopLen,
        bunchedBimonoidRowListGetMap (fun row => List.replicate topBlock.cols 0 ++ row) bottomBlock.entries
          (rowIndex - topBlock.rows) shiftedInRange,
        bunchedBimonoidListLengthAppend, bunchedBimonoidListLengthReplicate,
        wfBottom.2 (rowIndex - topBlock.rows) (by rw [← wfBottom.1]; exact shiftedInRange)]

/-! # =========================================================================================
    # THE MATRIX EXTENSIONALITY BY ENTRIES (via reconstruction + eta; no List (List Nat) ext)
    # =========================================================================================
-/

/-- ★★ **Matrix extensionality by `matEntryAt`.**  Two well-formed matrices with equal `rows`, `cols`, and equal
entries at every in-range `(rowIndex, colIndex)` are equal.  Proved via the shipped `bunchedBimonoidMatReconstruct`
(each matrix's entries rebuild as a `List.range`-double-map of its own gets) + two range-map congruences down to the
per-entry equality, then `bunchedBimonoidMatEqOfEntries` — dodging abstract `List (List Nat)` extensionality. -/
theorem bunchedBimonoidMatExtByEntries (matA matB : BunchedBimonoidMat)
    (wfA : bunchedBimonoidMatWellFormed matA) (wfB : bunchedBimonoidMatWellFormed matB)
    (rowsEq : matA.rows = matB.rows) (colsEq : matA.cols = matB.cols)
    (entryEq : ∀ rowIndex colIndex, rowIndex < matA.rows → colIndex < matA.cols →
      bunchedBimonoidMatEntryAt matA rowIndex colIndex = bunchedBimonoidMatEntryAt matB rowIndex colIndex) :
    matA = matB := by
  apply bunchedBimonoidMatEqOfEntries matA matB rowsEq colsEq
  rw [← bunchedBimonoidMatReconstruct matA wfA, ← bunchedBimonoidMatReconstruct matB wfB, rowsEq, colsEq]
  apply bunchedBimonoidRangeMapCongr
  intro rowIndex rowBelow
  apply bunchedBimonoidRangeMapCongr
  intro colIndex colBelow
  exact entryEq rowIndex colIndex (by rw [rowsEq]; exact rowBelow) (by rw [colsEq]; exact colBelow)

/-! # =========================================================================================
    # A-ARITH — the shift arithmetic + swapValue bounds gate (a)'s bottom-right region needs
    # =========================================================================================
-/

/-- **Reassemble above the two-block** — for `k + 2 <= a`, `a = (k + 2) + (a - k - 2)`; the additive normal form
that recovers `a` from its shifted `identityMat (width - k - 2)` index.  Via `Nat.le.dest` + the shipped additive
left-cancels; propext-clean. -/
theorem bunchedBimonoidReassembleAboveTwo (k a : Nat) (hAbove : k + 2 ≤ a) :
    a = (k + 2) + (a - k - 2) := by
  obtain ⟨diff, hdiff⟩ := Nat.le.dest hAbove
  have hstep : a - k - 2 = diff := by
    rw [← hdiff, Nat.add_assoc k 2 diff, bunchedBimonoidAddSubCancelLeft k (2 + diff),
      bunchedBimonoidAddSubCancelLeft 2 diff]
  rw [hstep]; exact hdiff.symm

/-- **The shifted delta cancels the two-block shift** — for `k + 2 <= a` and `k + 2 <= b`,
`(a - k - 2 == b - k - 2) = (a == b)`.  The bottom-right `identityMat (width - k - 2)` reads `[a-k-2 == b-k-2]`;
this is exactly `[a == b]` because the shift `(k + 2) + _` is injective.  Cases on `Nat.decEq a b`, dodging any
`propext` leak (self-`beq` via the shipped `natBeqSelf`, the negative via `decideEqFalse` + reassemble). -/
theorem bunchedBimonoidShiftBeqCancel (k a b : Nat) (hAboveA : k + 2 ≤ a) (hAboveB : k + 2 ≤ b) :
    (a - k - 2 == b - k - 2) = (a == b) := by
  rcases Nat.decEq a b with hab | hab
  · have rhsFalse : (a == b) = false := bunchedBimonoidDecideEqFalse hab
    have lhsFalse : (a - k - 2 == b - k - 2) = false := by
      apply bunchedBimonoidDecideEqFalse
      intro hsub
      exact hab
        ((bunchedBimonoidReassembleAboveTwo k a hAboveA).trans
          ((congrArg (fun rest => (k + 2) + rest) hsub).trans
            (bunchedBimonoidReassembleAboveTwo k b hAboveB).symm))
    rw [lhsFalse, rhsFalse]
  · subst hab
    rw [bunchedBimonoidNatBeqSelf (a - k - 2), bunchedBimonoidNatBeqSelf a]

/-- **The shifted index stays below the bottom block** — for `k + 2 <= a`, `k + 2 <= width`, `a < width`,
`a - k - 2 < width - k - 2`; the bottom-right `identityMat (width - k - 2)` index stays in range.  Via reassemble
on both `a` and `width` + `Nat.lt_of_add_lt_add_left`. -/
theorem bunchedBimonoidSubTwoBelow (k a width : Nat) (hAboveA : k + 2 ≤ a) (hAboveWidth : k + 2 ≤ width)
    (hBelow : a < width) : a - k - 2 < width - k - 2 := by
  have reassembleA := bunchedBimonoidReassembleAboveTwo k a hAboveA
  have reassembleWidth := bunchedBimonoidReassembleAboveTwo k width hAboveWidth
  have shifted : (k + 2) + (a - k - 2) < (k + 2) + (width - k - 2) := by
    rw [← reassembleA, ← reassembleWidth]; exact hBelow
  exact Nat.lt_of_add_lt_add_left shifted

/-- **The value transposition stays at or above `k`** — for `k <= value`, `k <= swapValue k value`.  Whichever of
the three arms fires (`k+1`, `k`, or `value` itself) is `>= k`; the bottom bands of the block form use this to
refute a below-`k` column match. -/
theorem bunchedBimonoidSwapValueGeOfGe (k value : Nat) (hge : k ≤ value) :
    k ≤ bunchedBimonoidSwapValue k value := by
  show k ≤ (if value == k then k + 1 else if value == k + 1 then k else value)
  cases hvk : (value == k) with
  | true => exact Nat.le_succ k
  | false =>
    cases hvk1 : (value == k + 1) with
    | true => exact Nat.le_refl k
    | false => exact hge

/-- **Two below the shifted difference** — for `k + 2 <= a`, `2 <= a - k`; the bottom-right block index sits at or
above the `sigma2x2` block's two rows/cols.  Via `Nat.le.dest` + the additive left-cancel. -/
theorem bunchedBimonoidTwoLeSubOfAdd (k a : Nat) (hAbove : k + 2 ≤ a) : 2 ≤ a - k := by
  obtain ⟨diff, hdiff⟩ := Nat.le.dest hAbove
  have hstep : a - k = 2 + diff := by
    rw [← hdiff, Nat.add_assoc k 2 diff, bunchedBimonoidAddSubCancelLeft k (2 + diff)]
  rw [hstep]; exact Nat.le_add_right 2 diff

/-! # =========================================================================================
    # GATE (a) — `evalCell (sigmaAt width k) = permMatrixOf width (swap range k)` (entry-wise)
    # =========================================================================================
-/

/-- ★★★ **GATE (a) — `sigmaAt`-as-transposition, generic width.**  For `k + 2 <= width`,
`evalCell (sigmaAt width k) = permMatrixOf width (applyAdjacentSwap (List.range width) k)`.  The r11 wall's first
named gate.  Via the shipped closed block-form (`bunchedBimonoidSigmaAtBlockForm`) + `matExtByEntries`, then a
4-band index case split (`i < k`, `i = k`, `i = k + 1`, `i > k + 1`, each crossed with the `j`-bands) over the
`directSum` quadrant reads + `identityMatEntry` + the `sigma2x2` literal + RELABEL-GET; the bottom-right identity
band closes via the shift-`beq` cancellation.  Every band ties the block-form entry to `if swapValue k i == j`. -/
theorem bunchedBimonoidSigmaAtIsTransposition (width k : Nat) (hValid : k + 2 ≤ width) :
    bunchedBimonoidEvalCell (bunchedBimonoidSigmaAt width k)
      = bunchedBimonoidPermMatrixOf width (bunchedBimonoidApplyAdjacentSwap (List.range width) k) := by
  rw [bunchedBimonoidSigmaAtBlockForm width k]
  have wfIDk := bunchedBimonoidIdentityMatWellFormed k
  have wfIDr := bunchedBimonoidIdentityMatWellFormed (width - k - 2)
  have wfIB := bunchedBimonoidDirectSumWellFormed { rows := 2, cols := 2, entries := [[0, 1], [1, 0]] }
    (bunchedBimonoidIdentityMat (width - k - 2)) bunchedBimonoidSigma2x2WellFormed wfIDr
  have arith : k + (2 + (width - k - 2)) = width := bunchedBimonoidSigmaAtDimArith k width hValid
  refine bunchedBimonoidMatExtByEntries _ _
    (bunchedBimonoidDirectSumWellFormed (bunchedBimonoidIdentityMat k) _ wfIDk wfIB)
    (bunchedBimonoidPermMatrixWellFormed width (bunchedBimonoidApplyAdjacentSwap (List.range width) k))
    arith arith ?_
  intro rowIndex colIndex rowBelow colBelow
  have hiWidth : rowIndex < width := Nat.lt_of_lt_of_le rowBelow (Nat.le_of_eq arith)
  have hjWidth : colIndex < width := Nat.lt_of_lt_of_le colBelow (Nat.le_of_eq arith)
  have hk : k + 1 < width := hValid
  have hkk : k - k = 0 := bunchedBimonoidAddSubCancelLeft k 0
  have hk1k : k + 1 - k = 1 := bunchedBimonoidAddSubCancelLeft k 1
  have idkRows : (bunchedBimonoidIdentityMat k).rows = k := rfl
  have idkCols : (bunchedBimonoidIdentityMat k).cols = k := rfl
  have sigRows : ({ rows := 2, cols := 2, entries := [[0, 1], [1, 0]] } : BunchedBimonoidMat).rows = 2 := rfl
  have sigCols : ({ rows := 2, cols := 2, entries := [[0, 1], [1, 0]] } : BunchedBimonoidMat).cols = 2 := rfl
  rw [bunchedBimonoidPermMatrixEntryAt width (bunchedBimonoidApplyAdjacentSwap (List.range width) k)
      rowIndex colIndex hiWidth hjWidth,
    bunchedBimonoidGetApplyAdjacentSwapRange width k rowIndex hk hiWidth]
  -- Goal: matEntryAt blockForm i j = if swapValue k i == j then 1 else 0
  rcases Nat.lt_or_ge rowIndex k with hiLtK | hiGeK
  · -- i < k : outer top blocks; swapValue k i = i
    rw [bunchedBimonoidSwapValueElsewhere k rowIndex (Nat.ne_of_lt hiLtK)
        (Nat.ne_of_lt (Nat.lt_trans hiLtK (Nat.lt_succ_self k)))]
    rcases Nat.lt_or_ge colIndex k with hjLtK | hjGeK
    · rw [bunchedBimonoidDirectSumEntryTopLeft (bunchedBimonoidIdentityMat k) _ wfIDk rowIndex colIndex hiLtK hjLtK,
        bunchedBimonoidIdentityMatEntry k rowIndex colIndex hiLtK hjLtK]
    · rw [bunchedBimonoidDirectSumEntryTopRight (bunchedBimonoidIdentityMat k) _ wfIDk rowIndex colIndex hiLtK hjGeK,
        if_neg (fun heq => absurd (bunchedBimonoidNatEqOfBeqTrue _ _ heq)
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le hiLtK hjGeK)))]
  · -- i ≥ k
    rcases Nat.lt_or_ge rowIndex (k + 1) with hiLtK1 | hiGeK1
    · -- i = k : swapValue k k = k + 1
      have hiEqK : rowIndex = k := Nat.le_antisymm (Nat.le_of_lt_succ hiLtK1) hiGeK
      subst rowIndex
      rw [bunchedBimonoidSwapValueAtK k]
      rcases Nat.lt_or_ge colIndex k with hjLtK | hjGeK
      · rw [bunchedBimonoidDirectSumEntryBottomLeft (bunchedBimonoidIdentityMat k) _ wfIDk wfIB k colIndex hiGeK rowBelow hjLtK,
          if_neg (fun heq => absurd (bunchedBimonoidNatEqOfBeqTrue _ _ heq)
            (Nat.ne_of_gt (Nat.lt_trans hjLtK (Nat.lt_succ_self k))))]
      · rw [bunchedBimonoidDirectSumEntryBottomRight (bunchedBimonoidIdentityMat k) _ wfIDk wfIB k colIndex hiGeK rowBelow hjGeK,
          idkRows, idkCols, hkk]
        rcases Nat.lt_or_ge colIndex (k + 1) with hjLtK1 | hjGeK1
        · have hjEqK : colIndex = k := Nat.le_antisymm (Nat.le_of_lt_succ hjLtK1) hjGeK
          subst colIndex
          rw [hkk, bunchedBimonoidDirectSumEntryTopLeft _ _ bunchedBimonoidSigma2x2WellFormed 0 0 (by decide) (by decide)]
          show (0 : Nat) = if k + 1 == k then 1 else 0
          rw [if_neg (fun heq => absurd (bunchedBimonoidNatEqOfBeqTrue _ _ heq) (Nat.ne_of_gt (Nat.lt_succ_self k)))]
        · rcases Nat.lt_or_ge colIndex (k + 2) with hjLtK2 | hjGeK2
          · have hjEqK1 : colIndex = k + 1 := Nat.le_antisymm (Nat.le_of_lt_succ hjLtK2) hjGeK1
            subst colIndex
            rw [hk1k, bunchedBimonoidDirectSumEntryTopLeft _ _ bunchedBimonoidSigma2x2WellFormed 0 1 (by decide) (by decide)]
            show (1 : Nat) = if k + 1 == k + 1 then 1 else 0
            rw [if_pos (bunchedBimonoidNatBeqSelf (k + 1))]
          · rw [bunchedBimonoidDirectSumEntryTopRight _ _ bunchedBimonoidSigma2x2WellFormed 0 (colIndex - k)
              (by decide) (bunchedBimonoidTwoLeSubOfAdd k colIndex hjGeK2),
              if_neg (fun heq => absurd (bunchedBimonoidNatEqOfBeqTrue _ _ heq) (Nat.ne_of_lt hjGeK2))]
    · rcases Nat.lt_or_ge rowIndex (k + 2) with hiLtK2 | hiGeK2
      · -- i = k + 1 : swapValue k (k+1) = k
        have hiEqK1 : rowIndex = k + 1 := Nat.le_antisymm (Nat.le_of_lt_succ hiLtK2) hiGeK1
        subst rowIndex
        rw [bunchedBimonoidSwapValueAtKSucc k]
        rcases Nat.lt_or_ge colIndex k with hjLtK | hjGeK
        · rw [bunchedBimonoidDirectSumEntryBottomLeft (bunchedBimonoidIdentityMat k) _ wfIDk wfIB (k + 1) colIndex hiGeK rowBelow hjLtK,
            if_neg (fun heq => absurd (bunchedBimonoidNatEqOfBeqTrue _ _ heq) (Nat.ne_of_gt hjLtK))]
        · rw [bunchedBimonoidDirectSumEntryBottomRight (bunchedBimonoidIdentityMat k) _ wfIDk wfIB (k + 1) colIndex hiGeK rowBelow hjGeK,
            idkRows, idkCols, hk1k]
          rcases Nat.lt_or_ge colIndex (k + 1) with hjLtK1 | hjGeK1
          · have hjEqK : colIndex = k := Nat.le_antisymm (Nat.le_of_lt_succ hjLtK1) hjGeK
            subst colIndex
            rw [hkk, bunchedBimonoidDirectSumEntryTopLeft _ _ bunchedBimonoidSigma2x2WellFormed 1 0 (by decide) (by decide)]
            show (1 : Nat) = if k == k then 1 else 0
            rw [if_pos (bunchedBimonoidNatBeqSelf k)]
          · rcases Nat.lt_or_ge colIndex (k + 2) with hjLtK2 | hjGeK2
            · have hjEqK1 : colIndex = k + 1 := Nat.le_antisymm (Nat.le_of_lt_succ hjLtK2) hjGeK1
              subst colIndex
              rw [hk1k, bunchedBimonoidDirectSumEntryTopLeft _ _ bunchedBimonoidSigma2x2WellFormed 1 1 (by decide) (by decide)]
              show (0 : Nat) = if k == k + 1 then 1 else 0
              rw [if_neg (fun heq => absurd (bunchedBimonoidNatEqOfBeqTrue _ _ heq) (Nat.ne_of_lt (Nat.lt_succ_self k)))]
            · rw [bunchedBimonoidDirectSumEntryTopRight _ _ bunchedBimonoidSigma2x2WellFormed 1 (colIndex - k)
                (by decide) (bunchedBimonoidTwoLeSubOfAdd k colIndex hjGeK2),
                if_neg (fun heq => absurd (bunchedBimonoidNatEqOfBeqTrue _ _ heq)
                  (Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.le_succ k) hjGeK2)))]
      · -- i > k + 1 : swapValue k i = i
        have hne0 : rowIndex ≠ k := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.le_succ (k + 1)) hiGeK2)
        have hne1 : rowIndex ≠ k + 1 := Nat.ne_of_gt hiGeK2
        rw [bunchedBimonoidSwapValueElsewhere k rowIndex hne0 hne1]
        rcases Nat.lt_or_ge colIndex k with hjLtK | hjGeK
        · rw [bunchedBimonoidDirectSumEntryBottomLeft (bunchedBimonoidIdentityMat k) _ wfIDk wfIB rowIndex colIndex hiGeK rowBelow hjLtK,
            if_neg (fun heq => absurd (bunchedBimonoidNatEqOfBeqTrue _ _ heq)
              (Nat.ne_of_gt (Nat.lt_of_lt_of_le hjLtK (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.le_succ (k + 1)) hiGeK2)))))]
        · rw [bunchedBimonoidDirectSumEntryBottomRight (bunchedBimonoidIdentityMat k) _ wfIDk wfIB rowIndex colIndex hiGeK rowBelow hjGeK,
            idkRows, idkCols]
          have twoLeIRel : 2 ≤ rowIndex - k := bunchedBimonoidTwoLeSubOfAdd k rowIndex hiGeK2
          have iRelBelow : rowIndex - k < 2 + (width - k - 2) := bunchedBimonoidSubLtOfLtAdd hiGeK rowBelow
          rcases Nat.lt_or_ge colIndex (k + 1) with hjLtK1 | hjGeK1
          · have hjEqK : colIndex = k := Nat.le_antisymm (Nat.le_of_lt_succ hjLtK1) hjGeK
            subst colIndex
            rw [hkk, bunchedBimonoidDirectSumEntryBottomLeft _ _ bunchedBimonoidSigma2x2WellFormed wfIDr
              (rowIndex - k) 0 twoLeIRel iRelBelow (by decide),
              if_neg (fun heq => absurd (bunchedBimonoidNatEqOfBeqTrue _ _ heq) hne0)]
          · rcases Nat.lt_or_ge colIndex (k + 2) with hjLtK2 | hjGeK2
            · have hjEqK1 : colIndex = k + 1 := Nat.le_antisymm (Nat.le_of_lt_succ hjLtK2) hjGeK1
              subst colIndex
              rw [hk1k, bunchedBimonoidDirectSumEntryBottomLeft _ _ bunchedBimonoidSigma2x2WellFormed wfIDr
                (rowIndex - k) 1 twoLeIRel iRelBelow (by decide),
                if_neg (fun heq => absurd (bunchedBimonoidNatEqOfBeqTrue _ _ heq) hne1)]
            · rw [bunchedBimonoidDirectSumEntryBottomRight _ _ bunchedBimonoidSigma2x2WellFormed wfIDr
                (rowIndex - k) (colIndex - k) twoLeIRel iRelBelow (bunchedBimonoidTwoLeSubOfAdd k colIndex hjGeK2),
                sigRows, sigCols,
                bunchedBimonoidIdentityMatEntry (width - k - 2) (rowIndex - k - 2) (colIndex - k - 2)
                  (bunchedBimonoidSubTwoBelow k rowIndex width hiGeK2 hValid hiWidth)
                  (bunchedBimonoidSubTwoBelow k colIndex width hjGeK2 hValid hjWidth),
                bunchedBimonoidShiftBeqCancel k rowIndex colIndex hiGeK2 hjGeK2]

/-! # =========================================================================================
    # GATE (b) — the matMul column-swap law (indicator picks one term)
    # =========================================================================================
-/

/-- ★★★ **GATE (b) — the matMul column-swap law.**  `matMul (permMatrixOf width p) (permMatrixOf width
(applyAdjacentSwap (List.range width) k)) = permMatrixOf width (p.map (swapValue k))` for `k + 1 < width`, a
length-`width` permutation `p` with entries `< width`.  The r11 wall's second named gate.  Entry-wise via
`matMulEntryRead` (expose the contraction), `permMatrixEntryAt` + RELABEL-GET on each factor, then the LEFT delta
collapse picks the single term `c = p[i]`; the right side reads through `getMapNat`.  The finite-sum
"indicator-picks-one-term" argument. -/
theorem bunchedBimonoidMatMulColumnSwapLaw (width k : Nat) (perm : List Nat)
    (hk : k + 1 < width) (hLen : perm.length = width)
    (hBound : ∀ index, index < width → bunchedBimonoidNatListGet perm index < width) :
    bunchedBimonoidMatMul (bunchedBimonoidPermMatrixOf width perm)
        (bunchedBimonoidPermMatrixOf width (bunchedBimonoidApplyAdjacentSwap (List.range width) k))
      = bunchedBimonoidPermMatrixOf width (perm.map (bunchedBimonoidSwapValue k)) := by
  have tkRows : (bunchedBimonoidPermMatrixOf width (bunchedBimonoidApplyAdjacentSwap (List.range width) k)).rows
      = width := rfl
  refine bunchedBimonoidMatExtByEntries _ _
    (bunchedBimonoidMatMulWellFormed (bunchedBimonoidPermMatrixOf width perm)
      (bunchedBimonoidPermMatrixOf width (bunchedBimonoidApplyAdjacentSwap (List.range width) k)))
    (bunchedBimonoidPermMatrixWellFormed width (perm.map (bunchedBimonoidSwapValue k)))
    rfl rfl ?_
  intro rowIndex colIndex rowBelow colBelow
  have hiWidth : rowIndex < width := rowBelow
  have hjWidth : colIndex < width := colBelow
  rw [bunchedBimonoidMatMulEntryRead (bunchedBimonoidPermMatrixOf width perm)
      (bunchedBimonoidPermMatrixOf width (bunchedBimonoidApplyAdjacentSwap (List.range width) k))
      rowIndex colIndex hiWidth hjWidth, tkRows]
  rw [bunchedBimonoidRangeMapCongr
    (fun contractionIndex =>
      bunchedBimonoidMatEntryAt (bunchedBimonoidPermMatrixOf width perm) rowIndex contractionIndex
        * bunchedBimonoidMatEntryAt
            (bunchedBimonoidPermMatrixOf width (bunchedBimonoidApplyAdjacentSwap (List.range width) k))
            contractionIndex colIndex)
    (fun contractionIndex =>
      (if bunchedBimonoidNatListGet perm rowIndex == contractionIndex then 1 else 0)
        * (if bunchedBimonoidSwapValue k contractionIndex == colIndex then 1 else 0))
    width
    (fun contractionIndex hc => by
      dsimp only
      rw [bunchedBimonoidPermMatrixEntryAt width perm rowIndex contractionIndex hiWidth hc,
        bunchedBimonoidPermMatrixEntryAt width (bunchedBimonoidApplyAdjacentSwap (List.range width) k)
          contractionIndex colIndex hc hjWidth,
        bunchedBimonoidGetApplyAdjacentSwapRange width k contractionIndex hk hc])]
  rw [bunchedBimonoidDeltaCollapseLeft
    (fun contractionIndex => if bunchedBimonoidSwapValue k contractionIndex == colIndex then 1 else 0)
    width (bunchedBimonoidNatListGet perm rowIndex) (hBound rowIndex hiWidth)]
  rw [bunchedBimonoidPermMatrixEntryAt width (perm.map (bunchedBimonoidSwapValue k)) rowIndex colIndex hiWidth hjWidth,
    bunchedBimonoidGetMapNat (bunchedBimonoidSwapValue k) perm rowIndex (by rw [hLen]; exact hiWidth)]

end FX1Poly.Polygraph.Omega
