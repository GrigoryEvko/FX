-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractorKit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidNormalFormCensus

/-! # Polygraph/Omega/WalkingBunchedBimonoidAffineOffsetSemantics — the AFFINE (unit-offset) matrix semantics
and its composability-gated absorption of the FULL star scope (WP-PROP r30, #2033)

★★ **THE MISSING INVARIANT.**  The shipped `Mat(N)` evaluation `bunchedBimonoidEvalCell` is BLIND to the unit
generators' outputs: `eta_a` contributes NO path from any input, so a cell that feeds an `eta_a` into a `mu_a`
(`(a <| eta) ; mu : a.id => a`) evaluates to the SAME `[[1]]` as `id_a`.  The star scope
(`StrictAxiomRel union SoundRow union HexagonRow`) contains NO unit law that could cancel that `eta` — the
excised r2 `unitUnit` / `leftUnitAssoc` / `rightUnitAssoc` rows were the FALSE (end-mismatched) spellings, and
the surviving `rootUnitAssoc` / `rootCounitCoassoc` rows are mere disjoint-strand naturality squares.  This
file builds the invariant that SEES the difference: the **affine-augmented matrix**
`aug(cell) = [[1, 0], [offset, matrix]]` — a `(targetWidth+1) x (sourceWidth+1)` matrix over `N` whose extra
column-0 tracks, per output strand, the number of unit-generator paths feeding it.  Composition is plain
`matMul` on augmented matrices; whiskering is the POINTED direct sum (the affine header row/column is shared).

## The junk gate (why the absorption is composability-gated)

On the FREE carrier the strict rows fire on arbitrary — including non-composable — cells, and NO compositional
matrix-like semantics respects `whiskerRightFunctorial` there (the wire block's position depends on the junk
factor's declared width; a concrete junk pair separates the two legs even under the shipped plain evaluation).
The honest absorber therefore gates by the Bool composability fold `bunchedBimonoidAugCleanCell` (every
`vcomp`'s factors agree on their augmented interface): the target relation is "Clean-equivalence + augmented
equality GIVEN Clean", which IS a saturated congruence — junk instances of the strict rows are Clean-false on
both legs (vacuous), and Clean instances hold by the pointed block algebra proved here.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # A — SMALL HELPERS (beq bridges, beyond-range reads, canonical well-formedness)
    # =========================================================================================
-/

/-- `(0 == j) = false` for positive `j` — the header-delta rewrite bridge. -/
theorem bunchedBimonoidAugBeqZeroLeftFalseOfPos : (colIndex : Nat) → 0 < colIndex →
    ((0 : Nat) == colIndex) = false
  | _ + 1, _ => rfl

/-- `(i == 0) = false` for positive `i`. -/
theorem bunchedBimonoidAugBeqZeroRightFalseOfPos : (rowIndex : Nat) → 0 < rowIndex →
    ((rowIndex : Nat) == 0) = false
  | _ + 1, _ => rfl

/-- Reading a `List Nat` at or beyond its length is `0` — the defensive-getter tail fact. -/
theorem bunchedBimonoidAugNatListGetBeyond : (values : List Nat) → (index : Nat) →
    values.length ≤ index → bunchedBimonoidNatListGet values index = 0
  | [], _, _ => rfl
  | _ :: _, 0, beyond => absurd beyond (Nat.not_succ_le_zero _)
  | _ :: tail, index + 1, beyond =>
      bunchedBimonoidAugNatListGetBeyond tail index (Nat.le_of_succ_le_succ beyond)

/-- Reading a row list at or beyond its length is the empty row. -/
theorem bunchedBimonoidAugRowListGetBeyond : (rows : List (List Nat)) → (index : Nat) →
    rows.length ≤ index → bunchedBimonoidRowListGet rows index = []
  | [], _, _ => rfl
  | _ :: _, 0, beyond => absurd beyond (Nat.not_succ_le_zero _)
  | _ :: tail, index + 1, beyond =>
      bunchedBimonoidAugRowListGetBeyond tail index (Nat.le_of_succ_le_succ beyond)

/-- ★ **Canonically range-built matrices are well-formed** — the shape invariant every augmented evaluation
output carries (all six evaluation arms are `List.range`-built). -/
theorem bunchedBimonoidAugCanonicalWellFormed (rowCount colCount : Nat) (entryFun : Nat → Nat → Nat) :
    bunchedBimonoidMatWellFormed
      { rows := rowCount, cols := colCount,
        entries := (List.range rowCount).map (fun rowIndex =>
          (List.range colCount).map (fun colIndex => entryFun rowIndex colIndex)) } :=
  ⟨by
      show ((List.range rowCount).map (fun rowIndex =>
        (List.range colCount).map (fun colIndex => entryFun rowIndex colIndex))).length = rowCount
      rw [bunchedBimonoidListMapLength, bunchedBimonoidRangeLength],
    fun rowIndex rowBelow => by
      show (bunchedBimonoidRowListGet ((List.range rowCount).map (fun rowIx =>
        (List.range colCount).map (fun colIndex => entryFun rowIx colIndex))) rowIndex).length = colCount
      rw [bunchedBimonoidRowListGetRangeMap rowCount
        (fun rowIx => (List.range colCount).map (fun colIndex => entryFun rowIx colIndex)) rowIndex rowBelow]
      rw [bunchedBimonoidListMapLength, bunchedBimonoidRangeLength]⟩

/-- ★ **The canonical in-range entry read** — a range-built matrix reads its entry function. -/
theorem bunchedBimonoidAugCanonicalEntry (rowCount colCount : Nat) (entryFun : Nat → Nat → Nat)
    (rowIndex colIndex : Nat) (rowBelow : rowIndex < rowCount) (colBelow : colIndex < colCount) :
    bunchedBimonoidMatEntryAt
        { rows := rowCount, cols := colCount,
          entries := (List.range rowCount).map (fun rowIx =>
            (List.range colCount).map (fun colIx => entryFun rowIx colIx)) }
        rowIndex colIndex
      = entryFun rowIndex colIndex := by
  show bunchedBimonoidNatListGet
      (bunchedBimonoidRowListGet ((List.range rowCount).map (fun rowIx =>
        (List.range colCount).map (fun colIx => entryFun rowIx colIx))) rowIndex) colIndex
    = entryFun rowIndex colIndex
  rw [bunchedBimonoidRowListGetRangeMap rowCount
    (fun rowIx => (List.range colCount).map (fun colIx => entryFun rowIx colIx)) rowIndex rowBelow]
  rw [bunchedBimonoidNatListGetRangeMap colCount (fun colIx => entryFun rowIndex colIx) colIndex colBelow]

/-- **Beyond-row read of a well-formed matrix is `0`.** -/
theorem bunchedBimonoidAugEntryBeyondRow (matrix : BunchedBimonoidMat)
    (wf : bunchedBimonoidMatWellFormed matrix) (rowIndex colIndex : Nat)
    (rowBeyond : matrix.rows ≤ rowIndex) :
    bunchedBimonoidMatEntryAt matrix rowIndex colIndex = 0 := by
  show bunchedBimonoidNatListGet (bunchedBimonoidRowListGet matrix.entries rowIndex) colIndex = 0
  rw [bunchedBimonoidAugRowListGetBeyond matrix.entries rowIndex (by rw [wf.1]; exact rowBeyond)]
  rfl

/-- **Beyond-column read of a well-formed matrix is `0`.** -/
theorem bunchedBimonoidAugEntryBeyondCol (matrix : BunchedBimonoidMat)
    (wf : bunchedBimonoidMatWellFormed matrix) (rowIndex colIndex : Nat)
    (colBeyond : matrix.cols ≤ colIndex) :
    bunchedBimonoidMatEntryAt matrix rowIndex colIndex = 0 := by
  match Nat.lt_or_ge rowIndex matrix.rows with
  | Or.inl rowBelow =>
      show bunchedBimonoidNatListGet (bunchedBimonoidRowListGet matrix.entries rowIndex) colIndex = 0
      exact bunchedBimonoidAugNatListGetBeyond _ colIndex (by rw [wf.2 rowIndex rowBelow]; exact colBeyond)
  | Or.inr rowBeyond => exact bunchedBimonoidAugEntryBeyondRow matrix wf rowIndex colIndex rowBeyond

/-- Structural right-summand cancellation (propext-free; Init's cancel lemmas leak). -/
theorem bunchedBimonoidAugAddRightCancel (leftValue rightValue : Nat) :
    (base : Nat) → leftValue + base = rightValue + base → leftValue = rightValue
  | 0, agree => agree
  | base + 1, agree => bunchedBimonoidAugAddRightCancel leftValue rightValue base (Nat.succ.inj agree)

/-- Structural left-summand cancellation. -/
theorem bunchedBimonoidAugAddLeftCancel (base leftValue rightValue : Nat)
    (agree : base + leftValue = base + rightValue) : leftValue = rightValue := by
  refine bunchedBimonoidAugAddRightCancel leftValue rightValue base ?_
  rw [Nat.add_comm leftValue base, Nat.add_comm rightValue base]
  exact agree

/-- Structural left-summand cancellation for `<=` (propext-free). -/
theorem bunchedBimonoidAugLeOfAddLeAddLeft (base leftValue rightValue : Nat)
    (bounded : base + leftValue ≤ base + rightValue) : leftValue ≤ rightValue :=
  match Nat.le.dest bounded with
  | ⟨gap, gapEq⟩ => Nat.le.intro (bunchedBimonoidAugAddLeftCancel base (leftValue + gap) rightValue
      (by rw [← Nat.add_assoc base leftValue gap]; exact gapEq))

/-- ★ **The shifted delta collapse** `natListSum ((range n).map (fun s => coeff s * (if j == base + s then 1
else 0))) = coeff (j - base)` when `base <= j < base + n`, and `= 0` when `j` misses the window — the wire-block
contraction collapse (a delta whose position is an injective shift of the summation index). -/
theorem bunchedBimonoidAugShiftedDeltaCollapseHit (coeff : Nat → Nat) (base : Nat) :
    (count : Nat) → (offset : Nat) → offset < count →
    bunchedBimonoidNatListSum ((List.range count).map (fun shift =>
        coeff shift * (if (base + offset) == (base + shift) then 1 else 0)))
      = coeff offset
  | 0, _, offsetBelow => absurd offsetBelow (Nat.not_lt_zero _)
  | count + 1, offset, offsetBelow => by
      rw [bunchedBimonoidSumRangeSucc
        (fun shift => coeff shift * (if (base + offset) == (base + shift) then 1 else 0)) count]
      match Nat.lt_or_ge offset count with
      | Or.inl offsetLt =>
          rw [bunchedBimonoidAugShiftedDeltaCollapseHit coeff base count offset offsetLt,
            bunchedBimonoidDeltaMulRightNe (coeff count) (base + offset) (base + count)
              (fun hit => absurd (bunchedBimonoidAugAddLeftCancel base offset count hit)
                (Nat.ne_of_lt offsetLt))]
          rfl
      | Or.inr offsetGe =>
          have offsetEq : offset = count := Nat.le_antisymm (Nat.le_of_lt_succ offsetBelow) offsetGe
          have headZero : bunchedBimonoidNatListSum ((List.range count).map (fun shift =>
              coeff shift * (if (base + offset) == (base + shift) then 1 else 0))) = 0 := by
            rw [congrArg bunchedBimonoidNatListSum
              (bunchedBimonoidRangeMapCongr
                (fun shift => coeff shift * (if (base + offset) == (base + shift) then 1 else 0))
                (fun _ => 0) count
                (fun shift shiftBelow =>
                  bunchedBimonoidDeltaMulRightNe (coeff shift) (base + offset) (base + shift)
                    (fun hit => absurd (bunchedBimonoidAugAddLeftCancel base offset shift hit)
                      (offsetEq ▸ (Nat.ne_of_lt shiftBelow).symm))))]
            exact bunchedBimonoidNatListSumMapZero (List.range count)
          rw [headZero, bunchedBimonoidDeltaMulRightEq (coeff count) (base + offset) (base + count)
            (by rw [offsetEq]), offsetEq]
          exact Nat.zero_add (coeff count)

/-- The shifted delta collapse, miss case: the target sits BELOW the window. -/
theorem bunchedBimonoidAugShiftedDeltaCollapseMissLow (coeff : Nat → Nat) (base target : Nat)
    (targetLow : target < base) : (count : Nat) →
    bunchedBimonoidNatListSum ((List.range count).map (fun shift =>
        coeff shift * (if target == (base + shift) then 1 else 0)))
      = 0
  | 0 => rfl
  | count + 1 => by
      rw [bunchedBimonoidSumRangeSucc
        (fun shift => coeff shift * (if target == (base + shift) then 1 else 0)) count]
      rw [bunchedBimonoidAugShiftedDeltaCollapseMissLow coeff base target targetLow count,
        bunchedBimonoidDeltaMulRightNe (coeff count) target (base + count)
          (fun hit => absurd hit (Nat.ne_of_lt (Nat.lt_of_lt_of_le targetLow (Nat.le_add_right base count))))]

/-- The shifted delta collapse, miss case: the target sits AT or ABOVE the window's end. -/
theorem bunchedBimonoidAugShiftedDeltaCollapseMissHigh (coeff : Nat → Nat) (base target : Nat) :
    (count : Nat) → base + count ≤ target →
    bunchedBimonoidNatListSum ((List.range count).map (fun shift =>
        coeff shift * (if target == (base + shift) then 1 else 0)))
      = 0
  | 0, _ => rfl
  | count + 1, targetHigh => by
      rw [bunchedBimonoidSumRangeSucc
        (fun shift => coeff shift * (if target == (base + shift) then 1 else 0)) count]
      rw [bunchedBimonoidAugShiftedDeltaCollapseMissHigh coeff base target count
          (Nat.le_of_succ_le targetHigh),
        bunchedBimonoidDeltaMulRightNe (coeff count) target (base + count)
          (fun hit => Nat.not_succ_le_self (base + count)
            (by rw [hit] at targetHigh; exact targetHigh))]

/-! # =========================================================================================
    # B — THE AUGMENTED (AFFINE) EVALUATION: seeds, truncPad, pointed sums, the six-arm fold
    # =========================================================================================
-/

/-- ★ **The augmented generator seed table** — the affine block `[[1, 0], [offset, matrix]]` of each label.
The two UNIT labels (`addUnit`, `multUnit`) carry offset `1` (their output strand receives one unit path);
every other operation label carries offset `0` next to its shipped matrix.  The two colour labels default to
the augmented width-1 identity (they never label a 2-cell in a real term; harmless total default). -/
def bunchedBimonoidAugGenSeed : BunchedBIGenLabel → BunchedBimonoidMat
  | .additiveColour => { rows := 2, cols := 2, entries := [[1, 0], [0, 1]] }
  | .multColour => { rows := 2, cols := 2, entries := [[1, 0], [0, 1]] }
  | .addMult => { rows := 2, cols := 3, entries := [[1, 0, 0], [0, 1, 1]] }
  | .addUnit => { rows := 2, cols := 1, entries := [[1], [1]] }
  | .addComult => { rows := 3, cols := 2, entries := [[1, 0], [0, 1], [0, 1]] }
  | .addCounit => { rows := 1, cols := 2, entries := [[1, 0]] }
  | .addSwap => { rows := 3, cols := 3, entries := [[1, 0, 0], [0, 0, 1], [0, 1, 0]] }
  | .multMult => { rows := 2, cols := 3, entries := [[1, 0, 0], [0, 1, 1]] }
  | .multUnit => { rows := 2, cols := 1, entries := [[1], [1]] }

/-- **Truncate/pad a matrix to declared dimensions** — the canonical range-built re-read.  Applied to every
generator seed at its DECLARED boundary widths: a canonical generator reads its seed verbatim; a junk-declared
generator is repaired to its declared shape (reads beyond the seed are `0`). -/
def bunchedBimonoidAugTruncPad (rowCount colCount : Nat) (matrix : BunchedBimonoidMat) : BunchedBimonoidMat :=
  { rows := rowCount, cols := colCount,
    entries := (List.range rowCount).map (fun rowIndex =>
      (List.range colCount).map (fun colIndex => bunchedBimonoidMatEntryAt matrix rowIndex colIndex)) }

/-- ★ **The left-pointed entry formula** — the augmented block-diagonal with `wireCount` identity wires
inserted BETWEEN the affine header (row/column `0`) and the block: row `0` is the shared header `[1, 0, ...]`,
rows `1..wireCount` are the wires (Kronecker delta), rows past `wireCount` read the block at the shifted
index — its offset column stays glued to global column `0`. -/
def bunchedBimonoidAugPointedLeftEntry (wireCount : Nat) (block : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) : Nat :=
  if rowIndex == 0 then (if (0 : Nat) == colIndex then 1 else 0)
  else if rowIndex ≤ wireCount then (if rowIndex == colIndex then 1 else 0)
  else if colIndex == 0 then bunchedBimonoidMatEntryAt block (rowIndex - wireCount) 0
  else if colIndex ≤ wireCount then 0
  else bunchedBimonoidMatEntryAt block (rowIndex - wireCount) (colIndex - wireCount)

/-- The **left-pointed sum** — `wireCount` wires in front of an augmented block, sharing the affine point. -/
def bunchedBimonoidAugPointedLeft (wireCount : Nat) (block : BunchedBimonoidMat) : BunchedBimonoidMat :=
  { rows := wireCount + block.rows, cols := wireCount + block.cols,
    entries := (List.range (wireCount + block.rows)).map (fun rowIndex =>
      (List.range (wireCount + block.cols)).map (fun colIndex =>
        bunchedBimonoidAugPointedLeftEntry wireCount block rowIndex colIndex)) }

/-- ★ **The right-pointed entry formula** — the block (with its own header row/column `0` kept global) with
`wireCount` identity wires appended AFTER it. -/
def bunchedBimonoidAugPointedRightEntry (block : BunchedBimonoidMat) (rowIndex colIndex : Nat) : Nat :=
  if rowIndex < block.rows then
    (if colIndex < block.cols then bunchedBimonoidMatEntryAt block rowIndex colIndex else 0)
  else if colIndex == rowIndex - block.rows + block.cols then 1 else 0

/-- The **right-pointed sum** — an augmented block with `wireCount` trailing wires. -/
def bunchedBimonoidAugPointedRight (block : BunchedBimonoidMat) (wireCount : Nat) : BunchedBimonoidMat :=
  { rows := block.rows + wireCount, cols := block.cols + wireCount,
    entries := (List.range (block.rows + wireCount)).map (fun rowIndex =>
      (List.range (block.cols + wireCount)).map (fun colIndex =>
        bunchedBimonoidAugPointedRightEntry block rowIndex colIndex)) }

/-! ## The five augmented evaluation helpers and the fold (mirroring `bunchedBimonoidEvalCell`) -/

/-- Augmented generator evaluation: width at label-dim 0, the DECLARED-boundary-truncated augmented seed at
label-dim 1, `Unit` above. -/
def bunchedBimonoidEvalAugGen : (labelDim : Nat) → BunchedBIGenLabel →
    BunchedBimonoidEvalCarrier labelDim → BunchedBimonoidEvalCarrier labelDim →
    BunchedBimonoidEvalCarrier (labelDim + 1)
  | 0, label, _, _ => bunchedBimonoidGenWidth label
  | 1, label, sourceWidth, targetWidth =>
      bunchedBimonoidAugTruncPad (Nat.add targetWidth 1) (Nat.add sourceWidth 1)
        (bunchedBimonoidAugGenSeed label)
  | _ + 2, _, _, _ => ()

/-- Augmented identity evaluation: the width-`(w+1)` augmented identity at dim 1->2. -/
def bunchedBimonoidEvalAugId : (d : Nat) → BunchedBimonoidEvalCarrier d → BunchedBimonoidEvalCarrier (d + 1)
  | 0, _ => (0 : Nat)
  | 1, width => bunchedBimonoidIdentityMat (Nat.add width 1)
  | _ + 2, _ => ()

/-- Augmented vertical composition: width addition at dim 1, augmented `matMul` at dim 2. -/
def bunchedBimonoidEvalAugVcomp : (d : Nat) →
    BunchedBimonoidEvalCarrier (d + 1) → BunchedBimonoidEvalCarrier (d + 1) →
    BunchedBimonoidEvalCarrier (d + 1)
  | 0, leftWidth, rightWidth => Nat.add leftWidth rightWidth
  | 1, leftMatrix, rightMatrix => bunchedBimonoidMatMul rightMatrix leftMatrix
  | _ + 2, _, _ => ()

/-- Augmented left whisker: the left-pointed sum at dim 2. -/
def bunchedBimonoidEvalAugWhiskerLeft : (d : Nat) →
    BunchedBimonoidEvalCarrier (d + 1) → BunchedBimonoidEvalCarrier (d + 2) →
    BunchedBimonoidEvalCarrier (d + 2)
  | 0, whiskerWidth, cellMatrix => bunchedBimonoidAugPointedLeft whiskerWidth cellMatrix
  | _ + 1, _, _ => ()

/-- Augmented right whisker: the right-pointed sum at dim 2. -/
def bunchedBimonoidEvalAugWhiskerRight : (d : Nat) →
    BunchedBimonoidEvalCarrier (d + 2) → BunchedBimonoidEvalCarrier (d + 1) →
    BunchedBimonoidEvalCarrier (d + 2)
  | 0, cellMatrix, whiskerWidth => bunchedBimonoidAugPointedRight cellMatrix whiskerWidth
  | _ + 1, _, _ => ()

/-- ★★ **The augmented (affine) evaluation** — the six-arm structural fold into the shipped dimension motive:
widths at dim 1 (unchanged), the AFFINE-augmented `(targetWidth+1) x (sourceWidth+1)` matrix at dim 2 (column
`0` = the unit-offset column the plain evaluation cannot see), `Unit` elsewhere. -/
def bunchedBimonoidEvalAugCell : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim →
    BunchedBimonoidEvalCarrier dim
  | _, .ofMode _ => ()
  | _, .gen (dim := labelDim) label source target =>
      bunchedBimonoidEvalAugGen labelDim label
        (bunchedBimonoidEvalAugCell source) (bunchedBimonoidEvalAugCell target)
  | _, .id (dim := d) cell => bunchedBimonoidEvalAugId d (bunchedBimonoidEvalAugCell cell)
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidEvalAugVcomp d (bunchedBimonoidEvalAugCell leftCell)
        (bunchedBimonoidEvalAugCell rightCell)
  | _, .whiskerLeft (dim := d) whiskerCell cell =>
      bunchedBimonoidEvalAugWhiskerLeft d (bunchedBimonoidEvalAugCell whiskerCell)
        (bunchedBimonoidEvalAugCell cell)
  | _, .whiskerRight (dim := d) cell whiskerCell =>
      bunchedBimonoidEvalAugWhiskerRight d (bunchedBimonoidEvalAugCell cell)
        (bunchedBimonoidEvalAugCell whiskerCell)

/-- The augmented width of a 1-cell word (the dim-1 augmented evaluation, manifestly `Nat`). -/
def bunchedBimonoidAugWordWidth (word : CellExpr bunchedBimonoidOmegaComputad 1) : Nat :=
  bunchedBimonoidEvalAugCell word

/-! ## Truth probes — the augmented semantics separates what the plain matrix cannot -/

#eval bunchedBimonoidEvalAugCell bunchedBimonoidAddMuGen
#eval bunchedBimonoidEvalAugCell bunchedBimonoidAddEtaGen
#eval bunchedBimonoidEvalAugCell
  (CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEtaGen)
    bunchedBimonoidAddMuGen)
#eval bunchedBimonoidEvalAugCell (CellExpr.id bunchedBimonoidAdditiveGen)

/-- The augmented `mu_a` is its seed on the nose (declared boundaries match). -/
theorem bunchedBimonoidAugAddMuGenValue :
    bunchedBimonoidEvalAugCell bunchedBimonoidAddMuGen
      = { rows := 2, cols := 3, entries := [[1, 0, 0], [0, 1, 1]] } := rfl

/-- ★★ **THE SEPARATION VALUE** — the unit-into-multiplication cell `(a <| eta_a) ; mu_a` carries offset `1`
on its output strand: augmented value `[[1, 0], [1, 1]]`, differing from `id_a`'s `[[1, 0], [0, 1]]` in the
offset column — while their PLAIN matrices are both `[[1]]`. -/
theorem bunchedBimonoidAugUnitIntoMuValue :
    bunchedBimonoidEvalAugCell
        (CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEtaGen)
          bunchedBimonoidAddMuGen)
      = { rows := 2, cols := 2, entries := [[1, 0], [1, 1]] } := rfl

/-- The augmented identity cell value. -/
theorem bunchedBimonoidAugIdentityCellValue :
    bunchedBimonoidEvalAugCell (CellExpr.id bunchedBimonoidAdditiveGen)
      = bunchedBimonoidIdentityMat 2 := rfl

/-! # =========================================================================================
    # B2 — ZONE READ LEMMAS for the pointed sums (conditioned entry rewrites)
    # =========================================================================================
-/

/-- Left-pointed header row: `PLEntry k A 0 j = delta(0, j)`. -/
theorem bunchedBimonoidAugPointedLeftEntryHeader (wireCount : Nat) (block : BunchedBimonoidMat)
    (colIndex : Nat) :
    bunchedBimonoidAugPointedLeftEntry wireCount block 0 colIndex
      = (if (0 : Nat) == colIndex then 1 else 0) := rfl

/-- Left-pointed wire row: `PLEntry k A i j = delta(i, j)` for `0 < i <= k` (every column). -/
theorem bunchedBimonoidAugPointedLeftEntryWire (wireCount : Nat) (block : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowPos : 0 < rowIndex) (rowWire : rowIndex ≤ wireCount) :
    bunchedBimonoidAugPointedLeftEntry wireCount block rowIndex colIndex
      = (if rowIndex == colIndex then 1 else 0) := by
  show (if rowIndex == 0 then (if (0 : Nat) == colIndex then 1 else 0)
      else if rowIndex ≤ wireCount then (if rowIndex == colIndex then 1 else 0)
      else if colIndex == 0 then bunchedBimonoidMatEntryAt block (rowIndex - wireCount) 0
      else if colIndex ≤ wireCount then 0
      else bunchedBimonoidMatEntryAt block (rowIndex - wireCount) (colIndex - wireCount))
    = (if rowIndex == colIndex then 1 else 0)
  rw [if_neg (by
      rw [bunchedBimonoidAugBeqZeroRightFalseOfPos rowIndex rowPos]; exact Bool.false_ne_true)]
  rw [if_pos rowWire]

/-- Left-pointed block row, offset column: `PLEntry k A i 0 = A[i-k][0]` for `k < i`. -/
theorem bunchedBimonoidAugPointedLeftEntryBlockOffset (wireCount : Nat) (block : BunchedBimonoidMat)
    (rowIndex : Nat) (rowBlock : wireCount < rowIndex) :
    bunchedBimonoidAugPointedLeftEntry wireCount block rowIndex 0
      = bunchedBimonoidMatEntryAt block (rowIndex - wireCount) 0 := by
  show (if rowIndex == 0 then (if (0 : Nat) == (0 : Nat) then 1 else 0)
      else if rowIndex ≤ wireCount then (if rowIndex == (0 : Nat) then 1 else 0)
      else if (0 : Nat) == 0 then bunchedBimonoidMatEntryAt block (rowIndex - wireCount) 0
      else if (0 : Nat) ≤ wireCount then 0
      else bunchedBimonoidMatEntryAt block (rowIndex - wireCount) (0 - wireCount))
    = bunchedBimonoidMatEntryAt block (rowIndex - wireCount) 0
  rw [if_neg (by
      rw [bunchedBimonoidAugBeqZeroRightFalseOfPos rowIndex
        (Nat.lt_of_le_of_lt (Nat.zero_le wireCount) rowBlock)]
      exact Bool.false_ne_true)]
  rw [if_neg (fun rowWire => Nat.lt_irrefl wireCount (Nat.lt_of_lt_of_le rowBlock rowWire))]
  rw [if_pos (show ((0 : Nat) == 0) = true from rfl)]

/-- Left-pointed block row, wire column: `PLEntry k A i j = 0` for `k < i`, `0 < j <= k`. -/
theorem bunchedBimonoidAugPointedLeftEntryBlockWireCol (wireCount : Nat) (block : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBlock : wireCount < rowIndex)
    (colPos : 0 < colIndex) (colWire : colIndex ≤ wireCount) :
    bunchedBimonoidAugPointedLeftEntry wireCount block rowIndex colIndex = 0 := by
  show (if rowIndex == 0 then (if (0 : Nat) == colIndex then 1 else 0)
      else if rowIndex ≤ wireCount then (if rowIndex == colIndex then 1 else 0)
      else if colIndex == 0 then bunchedBimonoidMatEntryAt block (rowIndex - wireCount) 0
      else if colIndex ≤ wireCount then 0
      else bunchedBimonoidMatEntryAt block (rowIndex - wireCount) (colIndex - wireCount))
    = 0
  rw [if_neg (by
      rw [bunchedBimonoidAugBeqZeroRightFalseOfPos rowIndex
        (Nat.lt_of_le_of_lt (Nat.zero_le wireCount) rowBlock)]
      exact Bool.false_ne_true)]
  rw [if_neg (fun rowWire => Nat.lt_irrefl wireCount (Nat.lt_of_lt_of_le rowBlock rowWire))]
  rw [if_neg (by
      rw [bunchedBimonoidAugBeqZeroRightFalseOfPos colIndex colPos]; exact Bool.false_ne_true)]
  rw [if_pos colWire]

/-- Left-pointed block row, block column: `PLEntry k A i j = A[i-k][j-k]` for `k < i`, `k < j`. -/
theorem bunchedBimonoidAugPointedLeftEntryBlockBlock (wireCount : Nat) (block : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBlock : wireCount < rowIndex) (colBlock : wireCount < colIndex) :
    bunchedBimonoidAugPointedLeftEntry wireCount block rowIndex colIndex
      = bunchedBimonoidMatEntryAt block (rowIndex - wireCount) (colIndex - wireCount) := by
  show (if rowIndex == 0 then (if (0 : Nat) == colIndex then 1 else 0)
      else if rowIndex ≤ wireCount then (if rowIndex == colIndex then 1 else 0)
      else if colIndex == 0 then bunchedBimonoidMatEntryAt block (rowIndex - wireCount) 0
      else if colIndex ≤ wireCount then 0
      else bunchedBimonoidMatEntryAt block (rowIndex - wireCount) (colIndex - wireCount))
    = bunchedBimonoidMatEntryAt block (rowIndex - wireCount) (colIndex - wireCount)
  rw [if_neg (by
      rw [bunchedBimonoidAugBeqZeroRightFalseOfPos rowIndex
        (Nat.lt_of_le_of_lt (Nat.zero_le wireCount) rowBlock)]
      exact Bool.false_ne_true)]
  rw [if_neg (fun rowWire => Nat.lt_irrefl wireCount (Nat.lt_of_lt_of_le rowBlock rowWire))]
  rw [if_neg (by
      rw [bunchedBimonoidAugBeqZeroRightFalseOfPos colIndex
        (Nat.lt_of_le_of_lt (Nat.zero_le wireCount) colBlock)]
      exact Bool.false_ne_true)]
  rw [if_neg (fun colWire => Nat.lt_irrefl wireCount (Nat.lt_of_lt_of_le colBlock colWire))]

/-- Right-pointed block zone: `PREntry A i j = A[i][j]` for `i < A.rows`, `j < A.cols`. -/
theorem bunchedBimonoidAugPointedRightEntryBlock (block : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBelow : rowIndex < block.rows) (colBelow : colIndex < block.cols) :
    bunchedBimonoidAugPointedRightEntry block rowIndex colIndex
      = bunchedBimonoidMatEntryAt block rowIndex colIndex := by
  show (if rowIndex < block.rows then
      (if colIndex < block.cols then bunchedBimonoidMatEntryAt block rowIndex colIndex else 0)
      else if colIndex == rowIndex - block.rows + block.cols then 1 else 0)
    = bunchedBimonoidMatEntryAt block rowIndex colIndex
  rw [if_pos rowBelow, if_pos colBelow]

/-- Right-pointed block row past the block columns: `PREntry A i j = 0` for `i < A.rows`, `A.cols <= j`. -/
theorem bunchedBimonoidAugPointedRightEntryBlockPad (block : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBelow : rowIndex < block.rows) (colBeyond : block.cols ≤ colIndex) :
    bunchedBimonoidAugPointedRightEntry block rowIndex colIndex = 0 := by
  show (if rowIndex < block.rows then
      (if colIndex < block.cols then bunchedBimonoidMatEntryAt block rowIndex colIndex else 0)
      else if colIndex == rowIndex - block.rows + block.cols then 1 else 0)
    = 0
  rw [if_pos rowBelow, if_neg (fun colBelow => Nat.lt_irrefl colIndex
    (Nat.lt_of_lt_of_le colBelow colBeyond))]

/-- Right-pointed wire row: `PREntry A i j = delta(j, (i - A.rows) + A.cols)` for `A.rows <= i`. -/
theorem bunchedBimonoidAugPointedRightEntryWire (block : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowWire : block.rows ≤ rowIndex) :
    bunchedBimonoidAugPointedRightEntry block rowIndex colIndex
      = (if colIndex == rowIndex - block.rows + block.cols then 1 else 0) := by
  show (if rowIndex < block.rows then
      (if colIndex < block.cols then bunchedBimonoidMatEntryAt block rowIndex colIndex else 0)
      else if colIndex == rowIndex - block.rows + block.cols then 1 else 0)
    = (if colIndex == rowIndex - block.rows + block.cols then 1 else 0)
  rw [if_neg (fun rowBelow => Nat.lt_irrefl rowIndex (Nat.lt_of_lt_of_le rowBelow rowWire))]

/-! ## The in-range record reads, specialized to the three canonical constructors -/

/-- In-range read of a `truncPad` output. -/
theorem bunchedBimonoidAugTruncPadEntry (rowCount colCount : Nat) (matrix : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBelow : rowIndex < rowCount) (colBelow : colIndex < colCount) :
    bunchedBimonoidMatEntryAt (bunchedBimonoidAugTruncPad rowCount colCount matrix) rowIndex colIndex
      = bunchedBimonoidMatEntryAt matrix rowIndex colIndex :=
  bunchedBimonoidAugCanonicalEntry rowCount colCount
    (fun rowIx colIx => bunchedBimonoidMatEntryAt matrix rowIx colIx) rowIndex colIndex rowBelow colBelow

/-- In-range read of a left-pointed sum. -/
theorem bunchedBimonoidAugPointedLeftRead (wireCount : Nat) (block : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBelow : rowIndex < wireCount + block.rows)
    (colBelow : colIndex < wireCount + block.cols) :
    bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedLeft wireCount block) rowIndex colIndex
      = bunchedBimonoidAugPointedLeftEntry wireCount block rowIndex colIndex :=
  bunchedBimonoidAugCanonicalEntry (wireCount + block.rows) (wireCount + block.cols)
    (bunchedBimonoidAugPointedLeftEntry wireCount block) rowIndex colIndex rowBelow colBelow

/-- In-range read of a right-pointed sum. -/
theorem bunchedBimonoidAugPointedRightRead (block : BunchedBimonoidMat) (wireCount : Nat)
    (rowIndex colIndex : Nat) (rowBelow : rowIndex < block.rows + wireCount)
    (colBelow : colIndex < block.cols + wireCount) :
    bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedRight block wireCount) rowIndex colIndex
      = bunchedBimonoidAugPointedRightEntry block rowIndex colIndex :=
  bunchedBimonoidAugCanonicalEntry (block.rows + wireCount) (block.cols + wireCount)
    (bunchedBimonoidAugPointedRightEntry block) rowIndex colIndex rowBelow colBelow

/-! # =========================================================================================
    # C — THE CLEAN GATE + THE THREE STRUCTURAL INVARIANTS (shape, boundary dims, headedness)
    # =========================================================================================
-/

/-- Bool conjunction split (monomorphic, propext-free). -/
theorem bunchedBimonoidAugAndSplit : {leftFlag rightFlag : Bool} → ((leftFlag && rightFlag) = true) →
    leftFlag = true ∧ rightFlag = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, both => absurd both (fun bad => Bool.noConfusion bad)
  | false, _, both => absurd both (fun bad => Bool.noConfusion bad)

/-- Bool conjunction join. -/
theorem bunchedBimonoidAugAndJoin : {leftFlag rightFlag : Bool} → leftFlag = true → rightFlag = true →
    (leftFlag && rightFlag) = true
  | true, true, _, _ => rfl

/-- The **augmented composability gate**, dimension-matched: no constraint at the word level, augmented
interface agreement (`left.rows == right.cols`) at the matrix level, trivial above. -/
def bunchedBimonoidAugComposableBool : (d : Nat) →
    BunchedBimonoidEvalCarrier (d + 1) → BunchedBimonoidEvalCarrier (d + 1) → Bool
  | 0, _, _ => true
  | 1, leftMatrix, rightMatrix => leftMatrix.rows == rightMatrix.cols
  | _ + 2, _, _ => true

/-- ★ **The Clean gate** — the Bool fold demanding every vertical composite's factors agree on their augmented
interface.  Junk (non-composable) cells are exactly the Clean-false ones; the strict rows are absorbed by the
augmented semantics GATED on this predicate (they are semantically FALSE on junk instances — machine-checked
by `bunchedBimonoidAugRightFunctorialJunkSeparates`, the r31 additive append at the END of this file). -/
def bunchedBimonoidAugCleanCell : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Bool
  | _, .ofMode _ => true
  | _, .gen _ source target => bunchedBimonoidAugCleanCell source && bunchedBimonoidAugCleanCell target
  | _, .id cell => bunchedBimonoidAugCleanCell cell
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidAugCleanCell leftCell
        && (bunchedBimonoidAugCleanCell rightCell
          && bunchedBimonoidAugComposableBool d
              (bunchedBimonoidEvalAugCell leftCell) (bunchedBimonoidEvalAugCell rightCell))
  | _, .whiskerLeft whiskerCell cell =>
      bunchedBimonoidAugCleanCell whiskerCell && bunchedBimonoidAugCleanCell cell
  | _, .whiskerRight cell whiskerCell =>
      bunchedBimonoidAugCleanCell cell && bunchedBimonoidAugCleanCell whiskerCell

/-- The low-dimension cleanliness statement (Clean is unconditional below dimension 2). -/
def bunchedBimonoidAugCleanLowStatement : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Prop
  | 0, cell => bunchedBimonoidAugCleanCell cell = true
  | 1, cell => bunchedBimonoidAugCleanCell cell = true
  | _ + 2, _ => True

/-- Every cell of dimension `<= 1` is Clean (words carry no composability constraint). -/
theorem bunchedBimonoidAugCleanLow : ∀ {dim : Nat} (cell : CellExpr bunchedBimonoidOmegaComputad dim),
    bunchedBimonoidAugCleanLowStatement cell
  | _, .ofMode _ => rfl
  | _, .gen (dim := 0) _ source target =>
      bunchedBimonoidAugAndJoin (bunchedBimonoidAugCleanLow source) (bunchedBimonoidAugCleanLow target)
  | _, .gen (dim := _ + 1) _ _ _ => True.intro
  | _, .id (dim := 0) cell => bunchedBimonoidAugCleanLow cell
  | _, .id (dim := _ + 1) _ => True.intro
  | _, .vcomp (dim := 0) leftCell rightCell =>
      bunchedBimonoidAugAndJoin (bunchedBimonoidAugCleanLow leftCell)
        (bunchedBimonoidAugAndJoin (bunchedBimonoidAugCleanLow rightCell) rfl)
  | _, .vcomp (dim := _ + 1) _ _ => True.intro
  | _, .whiskerLeft _ _ => True.intro
  | _, .whiskerRight _ _ => True.intro

/-- The dim-1 cleanliness wrapper: every word is Clean. -/
theorem bunchedBimonoidAugCleanOneCell (word : CellExpr bunchedBimonoidOmegaComputad 1) :
    bunchedBimonoidAugCleanCell word = true :=
  bunchedBimonoidAugCleanLow word

/-! ## Shape: every augmented evaluation output is well-formed (head-level canonicality) -/

/-- `matMul` outputs are well-formed (range-built). -/
theorem bunchedBimonoidAugMatMulWellFormed (later earlier : BunchedBimonoidMat) :
    bunchedBimonoidMatWellFormed (bunchedBimonoidMatMul later earlier) :=
  bunchedBimonoidAugCanonicalWellFormed later.rows earlier.cols _

/-- `identityMat` is well-formed (range-built). -/
theorem bunchedBimonoidAugIdentityMatWellFormed (dimension : Nat) :
    bunchedBimonoidMatWellFormed (bunchedBimonoidIdentityMat dimension) :=
  bunchedBimonoidAugCanonicalWellFormed dimension dimension _

/-- `truncPad` outputs are well-formed. -/
theorem bunchedBimonoidAugTruncPadWellFormed (rowCount colCount : Nat) (matrix : BunchedBimonoidMat) :
    bunchedBimonoidMatWellFormed (bunchedBimonoidAugTruncPad rowCount colCount matrix) :=
  bunchedBimonoidAugCanonicalWellFormed rowCount colCount _

/-- Left-pointed sums are well-formed. -/
theorem bunchedBimonoidAugPointedLeftWellFormed (wireCount : Nat) (block : BunchedBimonoidMat) :
    bunchedBimonoidMatWellFormed (bunchedBimonoidAugPointedLeft wireCount block) :=
  bunchedBimonoidAugCanonicalWellFormed (wireCount + block.rows) (wireCount + block.cols) _

/-- Right-pointed sums are well-formed. -/
theorem bunchedBimonoidAugPointedRightWellFormed (block : BunchedBimonoidMat) (wireCount : Nat) :
    bunchedBimonoidMatWellFormed (bunchedBimonoidAugPointedRight block wireCount) :=
  bunchedBimonoidAugCanonicalWellFormed (block.rows + wireCount) (block.cols + wireCount) _

/-- The shape statement, dimension-matched (`Mat` well-formedness at dim 2, trivial elsewhere). -/
def bunchedBimonoidAugShapedStatement : {dim : Nat} → BunchedBimonoidEvalCarrier dim → Prop
  | 0, _ => True
  | 1, _ => True
  | 2, matrix => bunchedBimonoidMatWellFormed matrix
  | _ + 3, _ => True

/-- ★ **Every augmented evaluation output is well-formed** — head-level: all six arms are range-built. -/
theorem bunchedBimonoidEvalAugCellShaped : ∀ {dim : Nat} (cell : CellExpr bunchedBimonoidOmegaComputad dim),
    bunchedBimonoidAugShapedStatement (bunchedBimonoidEvalAugCell cell)
  | _, .ofMode _ => True.intro
  | _, .gen (dim := 0) _ _ _ => True.intro
  | _, .gen (dim := 1) label source target =>
      bunchedBimonoidAugTruncPadWellFormed _ _ (bunchedBimonoidAugGenSeed label)
  | _, .gen (dim := _ + 2) _ _ _ => True.intro
  | _, .id (dim := 0) _ => True.intro
  | _, .id (dim := 1) cell => bunchedBimonoidAugIdentityMatWellFormed _
  | _, .id (dim := _ + 2) _ => True.intro
  | _, .vcomp (dim := 0) _ _ => True.intro
  | _, .vcomp (dim := 1) leftCell rightCell => bunchedBimonoidAugMatMulWellFormed _ _
  | _, .vcomp (dim := _ + 2) _ _ => True.intro
  | _, .whiskerLeft (dim := 0) whiskerCell cell => bunchedBimonoidAugPointedLeftWellFormed _ _
  | _, .whiskerLeft (dim := _ + 1) _ _ => True.intro
  | _, .whiskerRight (dim := 0) cell whiskerCell => bunchedBimonoidAugPointedRightWellFormed _ _
  | _, .whiskerRight (dim := _ + 1) _ _ => True.intro

/-- The dim-2 shape wrapper. -/
theorem bunchedBimonoidAugWellFormedEval (cell : CellExpr bunchedBimonoidOmegaComputad 2) :
    bunchedBimonoidMatWellFormed (bunchedBimonoidEvalAugCell cell) :=
  bunchedBimonoidEvalAugCellShaped cell

/-! ## Boundary dims: the augmented dimensions are DECLARED-boundary-driven on every cell -/

/-- The boundary-dims statement, dimension-matched. -/
def bunchedBimonoidAugBoundaryDimsStatement : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Prop
  | 0, _ => True
  | 1, _ => True
  | 2, cell =>
      (bunchedBimonoidEvalAugCell cell).rows
          = bunchedBimonoidAugWordWidth (boundaryTarget cell) + 1
        ∧ (bunchedBimonoidEvalAugCell cell).cols
          = bunchedBimonoidAugWordWidth (boundarySource cell) + 1
  | _ + 3, _ => True

/-- ★ **The augmented dimensions are declared-boundary-driven** — every dim-2 cell's augmented matrix has
`rows = targetWidth + 1`, `cols = sourceWidth + 1`, junk or not (the truncPad repairs generators; the
composites read their factors' declared interfaces). -/
theorem bunchedBimonoidAugBoundaryDims : ∀ {dim : Nat} (cell : CellExpr bunchedBimonoidOmegaComputad dim),
    bunchedBimonoidAugBoundaryDimsStatement cell
  | _, .ofMode _ => True.intro
  | _, .gen (dim := 0) _ _ _ => True.intro
  | _, .gen (dim := 1) label source target => ⟨rfl, rfl⟩
  | _, .gen (dim := _ + 2) _ _ _ => True.intro
  | _, .id (dim := 0) _ => True.intro
  | _, .id (dim := 1) cell => ⟨rfl, rfl⟩
  | _, .id (dim := _ + 2) _ => True.intro
  | _, .vcomp (dim := 0) _ _ => True.intro
  | _, .vcomp (dim := 1) leftCell rightCell =>
      ⟨(bunchedBimonoidAugBoundaryDims rightCell).1, (bunchedBimonoidAugBoundaryDims leftCell).2⟩
  | _, .vcomp (dim := _ + 2) _ _ => True.intro
  | _, .whiskerLeft (dim := 0) whiskerCell cell =>
      ⟨congrArg (fun n => bunchedBimonoidAugWordWidth whiskerCell + n)
          (bunchedBimonoidAugBoundaryDims cell).1,
        congrArg (fun n => bunchedBimonoidAugWordWidth whiskerCell + n)
          (bunchedBimonoidAugBoundaryDims cell).2⟩
  | _, .whiskerLeft (dim := _ + 1) _ _ => True.intro
  | _, .whiskerRight (dim := 0) cell whiskerCell =>
      ⟨by
          show (bunchedBimonoidEvalAugCell cell).rows + bunchedBimonoidAugWordWidth whiskerCell
            = (bunchedBimonoidAugWordWidth (boundaryTarget cell)
                + bunchedBimonoidAugWordWidth whiskerCell) + 1
          rw [(bunchedBimonoidAugBoundaryDims cell).1]
          exact Nat.succ_add (bunchedBimonoidAugWordWidth (boundaryTarget cell))
            (bunchedBimonoidAugWordWidth whiskerCell),
        by
          show (bunchedBimonoidEvalAugCell cell).cols + bunchedBimonoidAugWordWidth whiskerCell
            = (bunchedBimonoidAugWordWidth (boundarySource cell)
                + bunchedBimonoidAugWordWidth whiskerCell) + 1
          rw [(bunchedBimonoidAugBoundaryDims cell).2]
          exact Nat.succ_add (bunchedBimonoidAugWordWidth (boundarySource cell))
            (bunchedBimonoidAugWordWidth whiskerCell)⟩
  | _, .whiskerRight (dim := _ + 1) _ _ => True.intro

/-- The dim-2 rows extraction. -/
theorem bunchedBimonoidAugRowsEq (cell : CellExpr bunchedBimonoidOmegaComputad 2) :
    (bunchedBimonoidEvalAugCell cell).rows
      = bunchedBimonoidAugWordWidth (boundaryTarget cell) + 1 :=
  (bunchedBimonoidAugBoundaryDims cell).1

/-- The dim-2 cols extraction. -/
theorem bunchedBimonoidAugColsEq (cell : CellExpr bunchedBimonoidOmegaComputad 2) :
    (bunchedBimonoidEvalAugCell cell).cols
      = bunchedBimonoidAugWordWidth (boundarySource cell) + 1 :=
  (bunchedBimonoidAugBoundaryDims cell).2

/-- Row positivity of every dim-2 augmented value. -/
theorem bunchedBimonoidAugRowsPos (cell : CellExpr bunchedBimonoidOmegaComputad 2) :
    0 < (bunchedBimonoidEvalAugCell cell).rows := by
  rw [bunchedBimonoidAugRowsEq cell]
  exact Nat.zero_lt_succ _

/-- Column positivity of every dim-2 augmented value. -/
theorem bunchedBimonoidAugColsPos (cell : CellExpr bunchedBimonoidOmegaComputad 2) :
    0 < (bunchedBimonoidEvalAugCell cell).cols := by
  rw [bunchedBimonoidAugColsEq cell]
  exact Nat.zero_lt_succ _

/-! ## Headedness: row 0 of every dim-2 augmented value is the affine header `[1, 0, ...]` -/

/-- The pointwise headedness of an augmented matrix. -/
def bunchedBimonoidAugHeadedMat (matrix : BunchedBimonoidMat) : Prop :=
  ∀ (colIndex : Nat),
    bunchedBimonoidMatEntryAt matrix 0 colIndex = (if (0 : Nat) == colIndex then 1 else 0)

/-- The headedness statement, dimension-matched. -/
def bunchedBimonoidAugHeadedStatement : {dim : Nat} → BunchedBimonoidEvalCarrier dim → Prop
  | 0, _ => True
  | 1, _ => True
  | 2, matrix => bunchedBimonoidAugHeadedMat matrix
  | _ + 3, _ => True

/-- Every generator seed is headed (all nine rows-0 read `[1, 0, ...]`). -/
theorem bunchedBimonoidAugGenSeedHeaded : (label : BunchedBIGenLabel) → (colIndex : Nat) →
    bunchedBimonoidMatEntryAt (bunchedBimonoidAugGenSeed label) 0 colIndex
      = (if (0 : Nat) == colIndex then 1 else 0)
  | .additiveColour, 0 => rfl
  | .additiveColour, 1 => rfl
  | .additiveColour, _ + 2 => rfl
  | .multColour, 0 => rfl
  | .multColour, 1 => rfl
  | .multColour, _ + 2 => rfl
  | .addMult, 0 => rfl
  | .addMult, 1 => rfl
  | .addMult, 2 => rfl
  | .addMult, _ + 3 => rfl
  | .addUnit, 0 => rfl
  | .addUnit, _ + 1 => rfl
  | .addComult, 0 => rfl
  | .addComult, 1 => rfl
  | .addComult, _ + 2 => rfl
  | .addCounit, 0 => rfl
  | .addCounit, 1 => rfl
  | .addCounit, _ + 2 => rfl
  | .addSwap, 0 => rfl
  | .addSwap, 1 => rfl
  | .addSwap, 2 => rfl
  | .addSwap, _ + 3 => rfl
  | .multMult, 0 => rfl
  | .multMult, 1 => rfl
  | .multMult, 2 => rfl
  | .multMult, _ + 3 => rfl
  | .multUnit, 0 => rfl
  | .multUnit, _ + 1 => rfl

/-- ★ **Every dim-2 augmented value is headed** — structural induction; the composite arms collapse the
header through the delta reads. -/
theorem bunchedBimonoidEvalAugCellHeaded : ∀ {dim : Nat} (cell : CellExpr bunchedBimonoidOmegaComputad dim),
    bunchedBimonoidAugHeadedStatement (bunchedBimonoidEvalAugCell cell)
  | _, .ofMode _ => True.intro
  | _, .gen (dim := 0) _ _ _ => True.intro
  | _, .gen (dim := 1) label source target => fun colIndex => by
      show bunchedBimonoidMatEntryAt
          (bunchedBimonoidAugTruncPad (Nat.add (bunchedBimonoidEvalAugCell target) 1)
            (Nat.add (bunchedBimonoidEvalAugCell source) 1) (bunchedBimonoidAugGenSeed label))
          0 colIndex
        = (if (0 : Nat) == colIndex then 1 else 0)
      match Nat.lt_or_ge colIndex (Nat.add (bunchedBimonoidEvalAugCell source) 1) with
      | Or.inl colBelow =>
          rw [bunchedBimonoidAugTruncPadEntry (Nat.add (bunchedBimonoidEvalAugCell target) 1)
            (Nat.add (bunchedBimonoidEvalAugCell source) 1) (bunchedBimonoidAugGenSeed label)
            0 colIndex (Nat.zero_lt_succ _) colBelow]
          exact bunchedBimonoidAugGenSeedHeaded label colIndex
      | Or.inr colBeyond =>
          rw [bunchedBimonoidAugEntryBeyondCol
            (bunchedBimonoidAugTruncPad (Nat.add (bunchedBimonoidEvalAugCell target) 1)
              (Nat.add (bunchedBimonoidEvalAugCell source) 1) (bunchedBimonoidAugGenSeed label))
            (bunchedBimonoidAugTruncPadWellFormed _ _ (bunchedBimonoidAugGenSeed label)) 0 colIndex
            colBeyond]
          rw [bunchedBimonoidAugBeqZeroLeftFalseOfPos colIndex
            (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) colBeyond)]
          rfl
  | _, .gen (dim := _ + 2) _ _ _ => True.intro
  | _, .id (dim := 0) _ => True.intro
  | _, .id (dim := 1) cell => fun colIndex => by
      show bunchedBimonoidMatEntryAt (bunchedBimonoidIdentityMat (Nat.add (bunchedBimonoidEvalAugCell cell) 1))
          0 colIndex
        = (if (0 : Nat) == colIndex then 1 else 0)
      match Nat.lt_or_ge colIndex (Nat.add (bunchedBimonoidEvalAugCell cell) 1) with
      | Or.inl colBelow =>
          rw [bunchedBimonoidIdentityMatEntry (Nat.add (bunchedBimonoidEvalAugCell cell) 1) 0 colIndex
            (Nat.zero_lt_succ _) colBelow]
      | Or.inr colBeyond =>
          rw [bunchedBimonoidAugEntryBeyondCol
            (bunchedBimonoidIdentityMat (Nat.add (bunchedBimonoidEvalAugCell cell) 1))
            (bunchedBimonoidAugIdentityMatWellFormed _) 0 colIndex colBeyond]
          rw [bunchedBimonoidAugBeqZeroLeftFalseOfPos colIndex
            (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) colBeyond)]
          rfl
  | _, .id (dim := _ + 2) _ => True.intro
  | _, .vcomp (dim := 0) _ _ => True.intro
  | _, .vcomp (dim := 1) leftCell rightCell => fun colIndex => by
      show bunchedBimonoidMatEntryAt
          (bunchedBimonoidMatMul (bunchedBimonoidEvalAugCell rightCell)
            (bunchedBimonoidEvalAugCell leftCell)) 0 colIndex
        = (if (0 : Nat) == colIndex then 1 else 0)
      match Nat.lt_or_ge colIndex (bunchedBimonoidEvalAugCell leftCell).cols with
      | Or.inl colBelow =>
          rw [bunchedBimonoidMatMulEntryRead (bunchedBimonoidEvalAugCell rightCell)
            (bunchedBimonoidEvalAugCell leftCell) 0 colIndex (bunchedBimonoidAugRowsPos rightCell) colBelow]
          rw [congrArg bunchedBimonoidNatListSum
            (bunchedBimonoidRangeMapCongr
              (fun contractionIndex =>
                bunchedBimonoidMatEntryAt (bunchedBimonoidEvalAugCell rightCell) 0 contractionIndex
                  * bunchedBimonoidMatEntryAt (bunchedBimonoidEvalAugCell leftCell) contractionIndex colIndex)
              (fun contractionIndex =>
                (if (0 : Nat) == contractionIndex then 1 else 0)
                  * bunchedBimonoidMatEntryAt (bunchedBimonoidEvalAugCell leftCell) contractionIndex colIndex)
              (bunchedBimonoidEvalAugCell leftCell).rows
              (fun contractionIndex _ =>
                congrArg
                  (· * bunchedBimonoidMatEntryAt (bunchedBimonoidEvalAugCell leftCell) contractionIndex
                    colIndex)
                  (bunchedBimonoidEvalAugCellHeaded rightCell contractionIndex)))]
          rw [bunchedBimonoidDeltaCollapseLeft
            (fun contractionIndex =>
              bunchedBimonoidMatEntryAt (bunchedBimonoidEvalAugCell leftCell) contractionIndex colIndex)
            (bunchedBimonoidEvalAugCell leftCell).rows 0 (bunchedBimonoidAugRowsPos leftCell)]
          exact bunchedBimonoidEvalAugCellHeaded leftCell colIndex
      | Or.inr colBeyond =>
          rw [bunchedBimonoidAugEntryBeyondCol
            (bunchedBimonoidMatMul (bunchedBimonoidEvalAugCell rightCell)
              (bunchedBimonoidEvalAugCell leftCell))
            (bunchedBimonoidAugMatMulWellFormed _ _) 0 colIndex colBeyond]
          rw [bunchedBimonoidAugBeqZeroLeftFalseOfPos colIndex
            (Nat.lt_of_lt_of_le (bunchedBimonoidAugColsPos leftCell) colBeyond)]
          rfl
  | _, .vcomp (dim := _ + 2) _ _ => True.intro
  | _, .whiskerLeft (dim := 0) whiskerCell cell => fun colIndex => by
      show bunchedBimonoidMatEntryAt
          (bunchedBimonoidAugPointedLeft (bunchedBimonoidAugWordWidth whiskerCell)
            (bunchedBimonoidEvalAugCell cell)) 0 colIndex
        = (if (0 : Nat) == colIndex then 1 else 0)
      match Nat.lt_or_ge colIndex
        (bunchedBimonoidAugWordWidth whiskerCell + (bunchedBimonoidEvalAugCell cell).cols) with
      | Or.inl colBelow =>
          rw [bunchedBimonoidAugPointedLeftRead (bunchedBimonoidAugWordWidth whiskerCell)
            (bunchedBimonoidEvalAugCell cell) 0 colIndex
            (Nat.lt_of_lt_of_le (bunchedBimonoidAugRowsPos cell)
              (Nat.le_add_left (bunchedBimonoidEvalAugCell cell).rows _))
            colBelow]
          rfl
      | Or.inr colBeyond =>
          rw [bunchedBimonoidAugEntryBeyondCol
            (bunchedBimonoidAugPointedLeft (bunchedBimonoidAugWordWidth whiskerCell)
              (bunchedBimonoidEvalAugCell cell))
            (bunchedBimonoidAugPointedLeftWellFormed _ _) 0 colIndex colBeyond]
          rw [bunchedBimonoidAugBeqZeroLeftFalseOfPos colIndex
            (Nat.lt_of_lt_of_le
              (Nat.lt_of_lt_of_le (bunchedBimonoidAugColsPos cell)
                (Nat.le_add_left (bunchedBimonoidEvalAugCell cell).cols _))
              colBeyond)]
          rfl
  | _, .whiskerLeft (dim := _ + 1) _ _ => True.intro
  | _, .whiskerRight (dim := 0) cell whiskerCell => fun colIndex => by
      show bunchedBimonoidMatEntryAt
          (bunchedBimonoidAugPointedRight (bunchedBimonoidEvalAugCell cell)
            (bunchedBimonoidAugWordWidth whiskerCell)) 0 colIndex
        = (if (0 : Nat) == colIndex then 1 else 0)
      match Nat.lt_or_ge colIndex
        ((bunchedBimonoidEvalAugCell cell).cols + bunchedBimonoidAugWordWidth whiskerCell) with
      | Or.inl colBelow =>
          rw [bunchedBimonoidAugPointedRightRead (bunchedBimonoidEvalAugCell cell)
            (bunchedBimonoidAugWordWidth whiskerCell) 0 colIndex
            (Nat.lt_of_lt_of_le (bunchedBimonoidAugRowsPos cell)
              (Nat.le_add_right (bunchedBimonoidEvalAugCell cell).rows _))
            colBelow]
          match Nat.lt_or_ge colIndex (bunchedBimonoidEvalAugCell cell).cols with
          | Or.inl colInBlock =>
              rw [bunchedBimonoidAugPointedRightEntryBlock (bunchedBimonoidEvalAugCell cell) 0 colIndex
                (bunchedBimonoidAugRowsPos cell) colInBlock]
              exact bunchedBimonoidEvalAugCellHeaded cell colIndex
          | Or.inr colInPad =>
              rw [bunchedBimonoidAugPointedRightEntryBlockPad (bunchedBimonoidEvalAugCell cell) 0 colIndex
                (bunchedBimonoidAugRowsPos cell) colInPad]
              rw [bunchedBimonoidAugBeqZeroLeftFalseOfPos colIndex
                (Nat.lt_of_lt_of_le (bunchedBimonoidAugColsPos cell) colInPad)]
              rfl
      | Or.inr colBeyond =>
          rw [bunchedBimonoidAugEntryBeyondCol
            (bunchedBimonoidAugPointedRight (bunchedBimonoidEvalAugCell cell)
              (bunchedBimonoidAugWordWidth whiskerCell))
            (bunchedBimonoidAugPointedRightWellFormed _ _) 0 colIndex colBeyond]
          rw [bunchedBimonoidAugBeqZeroLeftFalseOfPos colIndex
            (Nat.lt_of_lt_of_le
              (Nat.lt_of_lt_of_le (bunchedBimonoidAugColsPos cell)
                (Nat.le_add_right (bunchedBimonoidEvalAugCell cell).cols _))
              colBeyond)]
          rfl
  | _, .whiskerRight (dim := _ + 1) _ _ => True.intro

/-- The dim-2 headedness wrapper. -/
theorem bunchedBimonoidAugHeadedEval (cell : CellExpr bunchedBimonoidOmegaComputad 2) :
    bunchedBimonoidAugHeadedMat (bunchedBimonoidEvalAugCell cell) :=
  bunchedBimonoidEvalAugCellHeaded cell

/-! # =========================================================================================
    # D1 — POINTWISE-TO-RECORD LIFTING + INDEX/DELTA TOOLKIT
    # =========================================================================================
-/

/-- ★ **Record equality from pointwise entries** — two well-formed matrices with equal dimensions and equal
in-range entries are equal records (via the shipped reconstruction). -/
theorem bunchedBimonoidAugMatEqOfPointwise (matA matB : BunchedBimonoidMat)
    (rowsEq : matA.rows = matB.rows) (colsEq : matA.cols = matB.cols)
    (wfA : bunchedBimonoidMatWellFormed matA) (wfB : bunchedBimonoidMatWellFormed matB)
    (pointwise : ∀ (rowIndex colIndex : Nat), rowIndex < matA.rows → colIndex < matA.cols →
      bunchedBimonoidMatEntryAt matA rowIndex colIndex = bunchedBimonoidMatEntryAt matB rowIndex colIndex) :
    matA = matB := by
  have entriesEq : matA.entries = matB.entries := by
    rw [← bunchedBimonoidMatReconstruct matA wfA, ← bunchedBimonoidMatReconstruct matB wfB]
    rw [← rowsEq, ← colsEq]
    exact bunchedBimonoidRangeMapCongr _ _ matA.rows (fun rowIndex rowBelow =>
      bunchedBimonoidRangeMapCongr _ _ matA.cols (fun colIndex colBelow =>
        pointwise rowIndex colIndex rowBelow colBelow))
  exact bunchedBimonoidMatEqOfEntries matA matB rowsEq colsEq entriesEq

/-- Kronecker-delta rewrite (equal indices). -/
theorem bunchedBimonoidAugDeltaEqOne (leftIndex rightIndex : Nat) (agree : leftIndex = rightIndex) :
    (if leftIndex == rightIndex then 1 else 0) = 1 := by
  rw [if_pos (show (leftIndex == rightIndex) = true from bunchedBimonoidDecideEqTrue agree)]

/-- Kronecker-delta rewrite (distinct indices). -/
theorem bunchedBimonoidAugDeltaNeZero (leftIndex rightIndex : Nat) (differ : leftIndex ≠ rightIndex) :
    (if leftIndex == rightIndex then 1 else 0) = 0 := by
  have condFalse : (leftIndex == rightIndex) = false := bunchedBimonoidDecideEqFalse differ
  rw [if_neg (by rw [condFalse]; exact Bool.false_ne_true)]

/-- The right-shift beq cancel `((a + shift) == (b + shift)) = (a == b)`. -/
theorem bunchedBimonoidAugBeqShiftCancelRight (leftValue rightValue shift : Nat) :
    ((leftValue + shift) == (rightValue + shift)) = (leftValue == rightValue) := by
  match Nat.decEq leftValue rightValue with
  | isTrue agree =>
      rw [show ((leftValue + shift) == (rightValue + shift)) = true from
          bunchedBimonoidDecideEqTrue (congrArg (fun value => value + shift) agree),
        show (leftValue == rightValue) = true from bunchedBimonoidDecideEqTrue agree]
  | isFalse differ =>
      rw [show ((leftValue + shift) == (rightValue + shift)) = false from
          bunchedBimonoidDecideEqFalse (fun shifted =>
            differ (bunchedBimonoidAugAddRightCancel leftValue rightValue shift shifted)),
        show (leftValue == rightValue) = false from bunchedBimonoidDecideEqFalse differ]

/-- The left-shift beq cancel `((shift + a) == (shift + b)) = (a == b)`. -/
theorem bunchedBimonoidAugBeqShiftCancelLeft (shift leftValue rightValue : Nat) :
    ((shift + leftValue) == (shift + rightValue)) = (leftValue == rightValue) := by
  rw [Nat.add_comm shift leftValue, Nat.add_comm shift rightValue]
  exact bunchedBimonoidAugBeqShiftCancelRight leftValue rightValue shift

/-- ★ **The pointed index splitter** — every index is the header (`0`), a wire (`[1, wireCount]`), or a
block-local coordinate (`(wireCount + 1) + localPre`). -/
theorem bunchedBimonoidAugPointedIndexSplit : (wireCount index : Nat) →
    index = 0 ∨ ((0 < index ∧ index ≤ wireCount)
      ∨ ∃ localPre, index = (wireCount + 1) + localPre)
  | _, 0 => Or.inl rfl
  | wireCount, index + 1 =>
      match Nat.lt_or_ge (index + 1) (wireCount + 1) with
      | Or.inl belowWire =>
          Or.inr (Or.inl ⟨Nat.zero_lt_succ index, Nat.le_of_lt_succ belowWire⟩)
      | Or.inr aboveWire =>
          match Nat.le.dest aboveWire with
          | ⟨localPre, localEq⟩ => Or.inr (Or.inr ⟨localPre, localEq.symm⟩)

/-- The plain block/tail index splitter at an arbitrary bound. -/
theorem bunchedBimonoidAugIndexSplit (bound index : Nat) :
    index < bound ∨ ∃ localIndex, index = bound + localIndex :=
  match Nat.lt_or_ge index bound with
  | Or.inl below => Or.inl below
  | Or.inr above =>
      match Nat.le.dest above with
      | ⟨localIndex, localEq⟩ => Or.inr ⟨localIndex, localEq.symm⟩

/-- ★ **The pointed contraction three-zone split** — a sum over `range (wireCount + (preRows + 1))` splits
into the header term, the wire zone, and the shifted block zone. -/
theorem bunchedBimonoidAugPointedContractionSplit (summand : Nat → Nat) (wireCount preRows : Nat) :
    bunchedBimonoidNatListSum ((List.range (wireCount + (preRows + 1))).map summand)
      = summand 0
        + (bunchedBimonoidNatListSum ((List.range wireCount).map (fun wireIndex => summand (wireIndex + 1)))
          + bunchedBimonoidNatListSum ((List.range preRows).map
              (fun blockIndex => summand ((blockIndex + 1) + wireCount)))) := by
  rw [show wireCount + (preRows + 1) = 1 + (wireCount + preRows) from
    (Nat.add_comm 1 (wireCount + preRows)).symm]
  rw [bunchedBimonoidNatListSumRangeAddSplit summand 1 (wireCount + preRows)]
  rw [bunchedBimonoidNatListSumRangeAddSplit (fun index => summand (index + 1)) wireCount preRows]
  refine congrArg (fun tailSum => summand 0 + tailSum) ?_
  refine congrArg (fun blockSum =>
    bunchedBimonoidNatListSum ((List.range wireCount).map (fun wireIndex => summand (wireIndex + 1)))
      + blockSum) ?_
  exact congrArg bunchedBimonoidNatListSum
    (bunchedBimonoidRangeMapCongr
      (fun blockIndex => summand ((blockIndex + wireCount) + 1))
      (fun blockIndex => summand ((blockIndex + 1) + wireCount))
      preRows
      (fun blockIndex _ => congrArg summand (Nat.succ_add blockIndex wireCount).symm))

/-- Sum of a range-mapped all-zero function. -/
theorem bunchedBimonoidAugSumRangeZero (count : Nat) (summand : Nat → Nat)
    (allZero : ∀ index, index < count → summand index = 0) :
    bunchedBimonoidNatListSum ((List.range count).map summand) = 0 := by
  rw [congrArg bunchedBimonoidNatListSum
    (bunchedBimonoidRangeMapCongr summand (fun _ => 0) count allZero)]
  exact bunchedBimonoidNatListSumMapZero (List.range count)

/-- Beq symmetry `(a == b) = (b == a)` (via the decidable dichotomy). -/
theorem bunchedBimonoidAugBeqSymm (leftValue rightValue : Nat) :
    (leftValue == rightValue) = (rightValue == leftValue) := by
  match Nat.decEq leftValue rightValue with
  | isTrue agree =>
      rw [show (leftValue == rightValue) = true from bunchedBimonoidDecideEqTrue agree,
        show (rightValue == leftValue) = true from bunchedBimonoidDecideEqTrue agree.symm]
  | isFalse differ =>
      rw [show (leftValue == rightValue) = false from bunchedBimonoidDecideEqFalse differ,
        show (rightValue == leftValue) = false from
          bunchedBimonoidDecideEqFalse (fun flipped => differ flipped.symm)]

/-- `pred n + 1 = n` for positive `n`. -/
theorem bunchedBimonoidAugSuccPredOfPos : (value : Nat) → 0 < value → Nat.pred value + 1 = value
  | _ + 1, _ => rfl

/-- The positive-dimension identity matrix is headed. -/
theorem bunchedBimonoidAugIdentityHeaded (preDim : Nat) :
    bunchedBimonoidAugHeadedMat (bunchedBimonoidIdentityMat (preDim + 1)) := fun colIndex => by
  match Nat.lt_or_ge colIndex (preDim + 1) with
  | Or.inl colBelow =>
      rw [bunchedBimonoidIdentityMatEntry (preDim + 1) 0 colIndex (Nat.zero_lt_succ _) colBelow]
  | Or.inr colBeyond =>
      rw [bunchedBimonoidAugEntryBeyondCol (bunchedBimonoidIdentityMat (preDim + 1))
        (bunchedBimonoidAugIdentityMatWellFormed _) 0 colIndex colBeyond]
      rw [bunchedBimonoidAugBeqZeroLeftFalseOfPos colIndex
        (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) colBeyond)]
      rfl

/-! # =========================================================================================
    # D2 — THE POINTED TENSOR: the shared-point block sum unifying both whisker constructors
    # =========================================================================================
-/

/-- ★ **The pointed-tensor entry formula** — the affine block sum of two AUGMENTED matrices sharing their
point: the top block keeps its own indices (including the global header row/column `0`); the bottom block's
rows/columns `1..` are appended, its offset column glued to global column `0`. -/
def bunchedBimonoidAugPointedTensorEntry (blockTop blockBottom : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) : Nat :=
  if rowIndex < blockTop.rows then
    (if colIndex < blockTop.cols then bunchedBimonoidMatEntryAt blockTop rowIndex colIndex else 0)
  else if colIndex == 0 then
    bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1) 0
  else if colIndex < blockTop.cols then 0
  else bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1)
    ((colIndex - blockTop.cols) + 1)

/-- The **pointed tensor** of two augmented matrices. -/
def bunchedBimonoidAugPointedTensor (blockTop blockBottom : BunchedBimonoidMat) : BunchedBimonoidMat :=
  { rows := blockTop.rows + Nat.pred blockBottom.rows,
    cols := blockTop.cols + Nat.pred blockBottom.cols,
    entries := (List.range (blockTop.rows + Nat.pred blockBottom.rows)).map (fun rowIndex =>
      (List.range (blockTop.cols + Nat.pred blockBottom.cols)).map (fun colIndex =>
        bunchedBimonoidAugPointedTensorEntry blockTop blockBottom rowIndex colIndex)) }

/-- Pointed tensors are well-formed. -/
theorem bunchedBimonoidAugPointedTensorWellFormed (blockTop blockBottom : BunchedBimonoidMat) :
    bunchedBimonoidMatWellFormed (bunchedBimonoidAugPointedTensor blockTop blockBottom) :=
  bunchedBimonoidAugCanonicalWellFormed _ _ _

/-- In-range read of a pointed tensor. -/
theorem bunchedBimonoidAugPointedTensorRead (blockTop blockBottom : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBelow : rowIndex < blockTop.rows + Nat.pred blockBottom.rows)
    (colBelow : colIndex < blockTop.cols + Nat.pred blockBottom.cols) :
    bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockTop blockBottom) rowIndex colIndex
      = bunchedBimonoidAugPointedTensorEntry blockTop blockBottom rowIndex colIndex :=
  bunchedBimonoidAugCanonicalEntry _ _ _ rowIndex colIndex rowBelow colBelow

/-! ## The zone rewrites of the pointed-tensor entry formula -/

/-- Top-block zone. -/
theorem bunchedBimonoidAugPointedTensorEntryTop (blockTop blockBottom : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBelow : rowIndex < blockTop.rows) (colBelow : colIndex < blockTop.cols) :
    bunchedBimonoidAugPointedTensorEntry blockTop blockBottom rowIndex colIndex
      = bunchedBimonoidMatEntryAt blockTop rowIndex colIndex := by
  show (if rowIndex < blockTop.rows then
      (if colIndex < blockTop.cols then bunchedBimonoidMatEntryAt blockTop rowIndex colIndex else 0)
      else if colIndex == 0 then
        bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1) 0
      else if colIndex < blockTop.cols then 0
      else bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1)
        ((colIndex - blockTop.cols) + 1))
    = bunchedBimonoidMatEntryAt blockTop rowIndex colIndex
  rw [if_pos rowBelow, if_pos colBelow]

/-- Top-row pad zone (top row, past the top block's columns). -/
theorem bunchedBimonoidAugPointedTensorEntryTopPad (blockTop blockBottom : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBelow : rowIndex < blockTop.rows) (colBeyond : blockTop.cols ≤ colIndex) :
    bunchedBimonoidAugPointedTensorEntry blockTop blockBottom rowIndex colIndex = 0 := by
  show (if rowIndex < blockTop.rows then
      (if colIndex < blockTop.cols then bunchedBimonoidMatEntryAt blockTop rowIndex colIndex else 0)
      else if colIndex == 0 then
        bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1) 0
      else if colIndex < blockTop.cols then 0
      else bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1)
        ((colIndex - blockTop.cols) + 1))
    = 0
  rw [if_pos rowBelow,
    if_neg (fun colBelow => Nat.lt_irrefl colIndex (Nat.lt_of_lt_of_le colBelow colBeyond))]

/-- Bottom-block offset zone (bottom row, global column 0). -/
theorem bunchedBimonoidAugPointedTensorEntryBottomOffset (blockTop blockBottom : BunchedBimonoidMat)
    (rowIndex : Nat) (rowBeyond : blockTop.rows ≤ rowIndex) :
    bunchedBimonoidAugPointedTensorEntry blockTop blockBottom rowIndex 0
      = bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1) 0 := by
  show (if rowIndex < blockTop.rows then
      (if (0 : Nat) < blockTop.cols then bunchedBimonoidMatEntryAt blockTop rowIndex 0 else 0)
      else if (0 : Nat) == 0 then
        bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1) 0
      else if (0 : Nat) < blockTop.cols then 0
      else bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1)
        ((0 - blockTop.cols) + 1))
    = bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1) 0
  rw [if_neg (fun rowBelow => Nat.lt_irrefl rowIndex (Nat.lt_of_lt_of_le rowBelow rowBeyond)),
    if_pos (show ((0 : Nat) == 0) = true from rfl)]

/-- Bottom-row wire-column zone (bottom row, positive column inside the top block's columns). -/
theorem bunchedBimonoidAugPointedTensorEntryBottomZero (blockTop blockBottom : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBeyond : blockTop.rows ≤ rowIndex)
    (colPos : 0 < colIndex) (colBelow : colIndex < blockTop.cols) :
    bunchedBimonoidAugPointedTensorEntry blockTop blockBottom rowIndex colIndex = 0 := by
  show (if rowIndex < blockTop.rows then
      (if colIndex < blockTop.cols then bunchedBimonoidMatEntryAt blockTop rowIndex colIndex else 0)
      else if colIndex == 0 then
        bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1) 0
      else if colIndex < blockTop.cols then 0
      else bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1)
        ((colIndex - blockTop.cols) + 1))
    = 0
  rw [if_neg (fun rowBelow => Nat.lt_irrefl rowIndex (Nat.lt_of_lt_of_le rowBelow rowBeyond)),
    if_neg (by
      rw [bunchedBimonoidAugBeqZeroRightFalseOfPos colIndex colPos]; exact Bool.false_ne_true),
    if_pos colBelow]

/-- Bottom-block zone (bottom row, past the top block's columns, positive column). -/
theorem bunchedBimonoidAugPointedTensorEntryBottomBlock (blockTop blockBottom : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBeyond : blockTop.rows ≤ rowIndex)
    (colPos : 0 < colIndex) (colBeyond : blockTop.cols ≤ colIndex) :
    bunchedBimonoidAugPointedTensorEntry blockTop blockBottom rowIndex colIndex
      = bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1)
          ((colIndex - blockTop.cols) + 1) := by
  show (if rowIndex < blockTop.rows then
      (if colIndex < blockTop.cols then bunchedBimonoidMatEntryAt blockTop rowIndex colIndex else 0)
      else if colIndex == 0 then
        bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1) 0
      else if colIndex < blockTop.cols then 0
      else bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1)
        ((colIndex - blockTop.cols) + 1))
    = bunchedBimonoidMatEntryAt blockBottom ((rowIndex - blockTop.rows) + 1)
        ((colIndex - blockTop.cols) + 1)
  rw [if_neg (fun rowBelow => Nat.lt_irrefl rowIndex (Nat.lt_of_lt_of_le rowBelow rowBeyond)),
    if_neg (by
      rw [bunchedBimonoidAugBeqZeroRightFalseOfPos colIndex colPos]; exact Bool.false_ne_true),
    if_neg (fun colBelow => Nat.lt_irrefl colIndex (Nat.lt_of_lt_of_le colBelow colBeyond))]

/-! ## The two bridges: both pointed whisker sums ARE pointed tensors with identity blocks -/

/-- Block-local subtraction rewrite `(k + 1) + p - k = p + 1`. -/
theorem bunchedBimonoidAugBlockLocalSub (wireCount localPre : Nat) :
    (wireCount + 1) + localPre - wireCount = localPre + 1 := by
  rw [Nat.add_assoc wireCount 1 localPre, bunchedBimonoidAddSubCancelLeft wireCount (1 + localPre),
    Nat.add_comm 1 localPre]

/-- ★ **The left-pointed sum IS the pointed tensor with an identity top block.** -/
theorem bunchedBimonoidAugPointedLeftAsTensor (wireCount : Nat) (block : BunchedBimonoidMat)
    (rowsPos : 0 < block.rows) (colsPos : 0 < block.cols) :
    bunchedBimonoidAugPointedLeft wireCount block
      = bunchedBimonoidAugPointedTensor (bunchedBimonoidIdentityMat (wireCount + 1)) block := by
  have rowsEq : wireCount + block.rows = (wireCount + 1) + Nat.pred block.rows := by
    rw [← bunchedBimonoidAugSuccPredOfPos block.rows rowsPos]
    exact (Nat.succ_add wireCount (Nat.pred block.rows)).symm
  have colsEq : wireCount + block.cols = (wireCount + 1) + Nat.pred block.cols := by
    rw [← bunchedBimonoidAugSuccPredOfPos block.cols colsPos]
    exact (Nat.succ_add wireCount (Nat.pred block.cols)).symm
  refine bunchedBimonoidAugMatEqOfPointwise _ _ rowsEq colsEq
    (bunchedBimonoidAugPointedLeftWellFormed wireCount block)
    (bunchedBimonoidAugPointedTensorWellFormed _ _) (fun rowIndex colIndex rowBelow colBelow => ?_)
  rw [bunchedBimonoidAugPointedLeftRead wireCount block rowIndex colIndex rowBelow colBelow]
  rw [bunchedBimonoidAugPointedTensorRead (bunchedBimonoidIdentityMat (wireCount + 1)) block
    rowIndex colIndex (rowsEq ▸ rowBelow) (colsEq ▸ colBelow)]
  match bunchedBimonoidAugPointedIndexSplit wireCount rowIndex with
  | Or.inl rowZero =>
      cases rowZero
      rw [bunchedBimonoidAugPointedLeftEntryHeader]
      match Nat.lt_or_ge colIndex (wireCount + 1) with
      | Or.inl colInTop =>
          rw [bunchedBimonoidAugPointedTensorEntryTop (bunchedBimonoidIdentityMat (wireCount + 1)) block
            0 colIndex (Nat.zero_lt_succ _) colInTop]
          rw [bunchedBimonoidIdentityMatEntry (wireCount + 1) 0 colIndex (Nat.zero_lt_succ _) colInTop]
      | Or.inr colPastTop =>
          rw [bunchedBimonoidAugPointedTensorEntryTopPad (bunchedBimonoidIdentityMat (wireCount + 1)) block
            0 colIndex (Nat.zero_lt_succ _) colPastTop]
          rw [bunchedBimonoidAugBeqZeroLeftFalseOfPos colIndex
            (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) colPastTop)]
          rfl
  | Or.inr (Or.inl wireZone) =>
      rw [bunchedBimonoidAugPointedLeftEntryWire wireCount block rowIndex colIndex wireZone.1 wireZone.2]
      match Nat.lt_or_ge colIndex (wireCount + 1) with
      | Or.inl colInTop =>
          rw [bunchedBimonoidAugPointedTensorEntryTop (bunchedBimonoidIdentityMat (wireCount + 1)) block
            rowIndex colIndex (Nat.lt_succ_of_le wireZone.2) colInTop]
          rw [bunchedBimonoidIdentityMatEntry (wireCount + 1) rowIndex colIndex
            (Nat.lt_succ_of_le wireZone.2) colInTop]
      | Or.inr colPastTop =>
          rw [bunchedBimonoidAugPointedTensorEntryTopPad (bunchedBimonoidIdentityMat (wireCount + 1)) block
            rowIndex colIndex (Nat.lt_succ_of_le wireZone.2) colPastTop]
          exact bunchedBimonoidAugDeltaNeZero rowIndex colIndex
            (Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le wireZone.2) colPastTop))
  | Or.inr (Or.inr ⟨rowPre, rowEq⟩) =>
      cases rowEq
      have rowPastWires : wireCount < (wireCount + 1) + rowPre :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self wireCount) (Nat.le_add_right (wireCount + 1) rowPre)
      have rowPastTop : wireCount + 1 ≤ (wireCount + 1) + rowPre := Nat.le_add_right _ _
      match bunchedBimonoidAugPointedIndexSplit wireCount colIndex with
      | Or.inl colZero =>
          cases colZero
          rw [bunchedBimonoidAugPointedLeftEntryBlockOffset wireCount block _ rowPastWires]
          rw [bunchedBimonoidAugPointedTensorEntryBottomOffset (bunchedBimonoidIdentityMat (wireCount + 1))
            block _ rowPastTop]
          rw [show (bunchedBimonoidIdentityMat (wireCount + 1)).rows = wireCount + 1 from rfl]
          rw [bunchedBimonoidAugBlockLocalSub wireCount rowPre,
            bunchedBimonoidAddSubCancelLeft (wireCount + 1) rowPre]
      | Or.inr (Or.inl colWireZone) =>
          rw [bunchedBimonoidAugPointedLeftEntryBlockWireCol wireCount block _ colIndex rowPastWires
            colWireZone.1 colWireZone.2]
          rw [bunchedBimonoidAugPointedTensorEntryBottomZero (bunchedBimonoidIdentityMat (wireCount + 1))
            block _ colIndex rowPastTop colWireZone.1 (Nat.lt_succ_of_le colWireZone.2)]
      | Or.inr (Or.inr ⟨colPre, colEq⟩) =>
          cases colEq
          have colPastWires : wireCount < (wireCount + 1) + colPre :=
            Nat.lt_of_lt_of_le (Nat.lt_succ_self wireCount) (Nat.le_add_right (wireCount + 1) colPre)
          rw [bunchedBimonoidAugPointedLeftEntryBlockBlock wireCount block _ _ rowPastWires colPastWires]
          rw [bunchedBimonoidAugPointedTensorEntryBottomBlock (bunchedBimonoidIdentityMat (wireCount + 1))
            block _ _ rowPastTop
            (Nat.lt_of_lt_of_le (Nat.zero_lt_succ wireCount) (Nat.le_add_right (wireCount + 1) colPre))
            (Nat.le_add_right _ _)]
          rw [show (bunchedBimonoidIdentityMat (wireCount + 1)).rows = wireCount + 1 from rfl,
            show (bunchedBimonoidIdentityMat (wireCount + 1)).cols = wireCount + 1 from rfl]
          rw [bunchedBimonoidAugBlockLocalSub wireCount rowPre,
            bunchedBimonoidAugBlockLocalSub wireCount colPre,
            bunchedBimonoidAddSubCancelLeft (wireCount + 1) rowPre,
            bunchedBimonoidAddSubCancelLeft (wireCount + 1) colPre]

/-- ★ **The right-pointed sum IS the pointed tensor with an identity bottom block.** -/
theorem bunchedBimonoidAugPointedRightAsTensor (block : BunchedBimonoidMat) (wireCount : Nat)
    (colsPos : 0 < block.cols) :
    bunchedBimonoidAugPointedRight block wireCount
      = bunchedBimonoidAugPointedTensor block (bunchedBimonoidIdentityMat (wireCount + 1)) := by
  refine bunchedBimonoidAugMatEqOfPointwise _ _ rfl rfl
    (bunchedBimonoidAugPointedRightWellFormed block wireCount)
    (bunchedBimonoidAugPointedTensorWellFormed _ _) (fun rowIndex colIndex rowBelow colBelow => ?_)
  rw [bunchedBimonoidAugPointedRightRead block wireCount rowIndex colIndex rowBelow colBelow]
  rw [bunchedBimonoidAugPointedTensorRead block (bunchedBimonoidIdentityMat (wireCount + 1))
    rowIndex colIndex rowBelow colBelow]
  match bunchedBimonoidAugIndexSplit block.rows rowIndex with
  | Or.inl rowInBlock =>
      match Nat.lt_or_ge colIndex block.cols with
      | Or.inl colInBlock =>
          rw [bunchedBimonoidAugPointedRightEntryBlock block rowIndex colIndex rowInBlock colInBlock]
          rw [bunchedBimonoidAugPointedTensorEntryTop block (bunchedBimonoidIdentityMat (wireCount + 1))
            rowIndex colIndex rowInBlock colInBlock]
      | Or.inr colPastBlock =>
          rw [bunchedBimonoidAugPointedRightEntryBlockPad block rowIndex colIndex rowInBlock colPastBlock]
          rw [bunchedBimonoidAugPointedTensorEntryTopPad block (bunchedBimonoidIdentityMat (wireCount + 1))
            rowIndex colIndex rowInBlock colPastBlock]
  | Or.inr ⟨wireIndex, rowEq⟩ =>
      cases rowEq
      have rowPastBlock : block.rows ≤ block.rows + wireIndex := Nat.le_add_right _ _
      have wireBelow : wireIndex < wireCount :=
        Nat.lt_of_add_lt_add_left (show block.rows + wireIndex < block.rows + wireCount from rowBelow)
      rw [bunchedBimonoidAugPointedRightEntryWire block _ colIndex rowPastBlock]
      rw [bunchedBimonoidAddSubCancelLeft block.rows wireIndex]
      match bunchedBimonoidAugPointedIndexSplit 0 colIndex with
      | Or.inl colZero =>
          cases colZero
          rw [bunchedBimonoidAugPointedTensorEntryBottomOffset block
            (bunchedBimonoidIdentityMat (wireCount + 1)) _ rowPastBlock]
          rw [bunchedBimonoidAddSubCancelLeft block.rows wireIndex]
          rw [bunchedBimonoidIdentityMatEntry (wireCount + 1) (wireIndex + 1) 0
            (Nat.succ_lt_succ wireBelow) (Nat.zero_lt_succ _)]
          rw [bunchedBimonoidAugDeltaNeZero (wireIndex + 1) 0 (fun bad => Nat.noConfusion bad)]
          rw [bunchedBimonoidAugBeqZeroLeftFalseOfPos (wireIndex + block.cols)
            (Nat.lt_of_lt_of_le colsPos (Nat.le_add_left block.cols wireIndex))]
          rfl
      | Or.inr (Or.inl colBad) =>
          exact absurd colBad.2 (fun colLeZero =>
            Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le colBad.1 colLeZero))
      | Or.inr (Or.inr ⟨colLocal, colEq⟩) =>
          cases colEq
          match Nat.lt_or_ge (0 + 1 + colLocal) block.cols with
          | Or.inl colInBlockCols =>
              rw [bunchedBimonoidAugPointedTensorEntryBottomZero block
                (bunchedBimonoidIdentityMat (wireCount + 1)) _ _ rowPastBlock
                (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_add_right (0 + 1) colLocal))
                colInBlockCols]
              exact bunchedBimonoidAugDeltaNeZero _ _
                (Nat.ne_of_lt (Nat.lt_of_lt_of_le colInBlockCols (Nat.le_add_left block.cols wireIndex)))
          | Or.inr colPastBlockCols =>
              rw [bunchedBimonoidAugPointedTensorEntryBottomBlock block
                (bunchedBimonoidIdentityMat (wireCount + 1)) _ _ rowPastBlock
                (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_add_right (0 + 1) colLocal))
                colPastBlockCols]
              rw [bunchedBimonoidAddSubCancelLeft block.rows wireIndex]
              match Nat.le.dest colPastBlockCols with
              | ⟨colOffset, colSplit⟩ =>
                  rw [← colSplit, bunchedBimonoidAddSubCancelLeft block.cols colOffset]
                  rw [bunchedBimonoidIdentityMatEntry (wireCount + 1) (wireIndex + 1) (colOffset + 1)
                    (Nat.succ_lt_succ wireBelow)
                    (Nat.succ_lt_succ (Nat.lt_of_add_lt_add_left
                      (show block.cols + colOffset < block.cols + wireCount from colSplit ▸ colBelow)))]
                  rw [show ((wireIndex + 1) == (colOffset + 1)) = (wireIndex == colOffset) from
                    bunchedBimonoidAugBeqShiftCancelRight wireIndex colOffset 1]
                  rw [Nat.add_comm block.cols colOffset,
                    show ((colOffset + block.cols) == (wireIndex + block.cols))
                        = (colOffset == wireIndex) from
                      bunchedBimonoidAugBeqShiftCancelRight colOffset wireIndex block.cols]
                  rw [bunchedBimonoidAugBeqSymm colOffset wireIndex]

/-- ★ **The pointed tensor of two identities is the identity** `PT(I(m+1), I(n+1)) = I((m+1)+n)`. -/
theorem bunchedBimonoidAugPointedTensorIdentity (preTop preBottom : Nat) :
    bunchedBimonoidAugPointedTensor (bunchedBimonoidIdentityMat (preTop + 1))
        (bunchedBimonoidIdentityMat (preBottom + 1))
      = bunchedBimonoidIdentityMat ((preTop + 1) + preBottom) := by
  refine bunchedBimonoidAugMatEqOfPointwise _ _ rfl rfl
    (bunchedBimonoidAugPointedTensorWellFormed _ _)
    (bunchedBimonoidAugIdentityMatWellFormed _) (fun rowIndex colIndex rowBelow colBelow => ?_)
  rw [bunchedBimonoidAugPointedTensorRead (bunchedBimonoidIdentityMat (preTop + 1))
    (bunchedBimonoidIdentityMat (preBottom + 1)) rowIndex colIndex rowBelow colBelow]
  rw [bunchedBimonoidIdentityMatEntry ((preTop + 1) + preBottom) rowIndex colIndex rowBelow colBelow]
  match bunchedBimonoidAugIndexSplit (preTop + 1) rowIndex with
  | Or.inl rowInTop =>
      match Nat.lt_or_ge colIndex (preTop + 1) with
      | Or.inl colInTop =>
          rw [bunchedBimonoidAugPointedTensorEntryTop (bunchedBimonoidIdentityMat (preTop + 1))
            (bunchedBimonoidIdentityMat (preBottom + 1)) rowIndex colIndex rowInTop colInTop]
          rw [bunchedBimonoidIdentityMatEntry (preTop + 1) rowIndex colIndex rowInTop colInTop]
      | Or.inr colPastTop =>
          rw [bunchedBimonoidAugPointedTensorEntryTopPad (bunchedBimonoidIdentityMat (preTop + 1))
            (bunchedBimonoidIdentityMat (preBottom + 1)) rowIndex colIndex rowInTop colPastTop]
          exact (bunchedBimonoidAugDeltaNeZero rowIndex colIndex
            (Nat.ne_of_lt (Nat.lt_of_lt_of_le rowInTop colPastTop))).symm
  | Or.inr ⟨rowLocal, rowEq⟩ =>
      cases rowEq
      have rowPastTop : preTop + 1 ≤ (preTop + 1) + rowLocal := Nat.le_add_right _ _
      have rowLocalBelow : rowLocal < preBottom :=
        Nat.lt_of_add_lt_add_left (show (preTop + 1) + rowLocal < (preTop + 1) + preBottom from rowBelow)
      match bunchedBimonoidAugPointedIndexSplit preTop colIndex with
      | Or.inl colZero =>
          cases colZero
          rw [bunchedBimonoidAugPointedTensorEntryBottomOffset (bunchedBimonoidIdentityMat (preTop + 1))
            (bunchedBimonoidIdentityMat (preBottom + 1)) _ rowPastTop]
          rw [show (bunchedBimonoidIdentityMat (preTop + 1)).rows = preTop + 1 from rfl]
          rw [bunchedBimonoidAddSubCancelLeft (preTop + 1) rowLocal]
          rw [bunchedBimonoidIdentityMatEntry (preBottom + 1) (rowLocal + 1) 0
            (Nat.succ_lt_succ rowLocalBelow) (Nat.zero_lt_succ _)]
          rw [bunchedBimonoidAugDeltaNeZero (rowLocal + 1) 0 (fun bad => Nat.noConfusion bad)]
          exact (bunchedBimonoidAugDeltaNeZero _ 0
            (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ preTop)
              (Nat.le_add_right (preTop + 1) rowLocal)))).symm
      | Or.inr (Or.inl colWire) =>
          rw [bunchedBimonoidAugPointedTensorEntryBottomZero (bunchedBimonoidIdentityMat (preTop + 1))
            (bunchedBimonoidIdentityMat (preBottom + 1)) _ colIndex rowPastTop colWire.1
            (Nat.lt_succ_of_le colWire.2)]
          exact (bunchedBimonoidAugDeltaNeZero _ colIndex
            (Nat.ne_of_gt (Nat.lt_of_le_of_lt colWire.2
              (Nat.lt_of_lt_of_le (Nat.lt_succ_self preTop) (Nat.le_add_right (preTop + 1) rowLocal))))).symm
      | Or.inr (Or.inr ⟨colLocal, colEq⟩) =>
          cases colEq
          rw [bunchedBimonoidAugPointedTensorEntryBottomBlock (bunchedBimonoidIdentityMat (preTop + 1))
            (bunchedBimonoidIdentityMat (preBottom + 1)) _ _ rowPastTop
            (Nat.lt_of_lt_of_le (Nat.zero_lt_succ preTop) (Nat.le_add_right (preTop + 1) colLocal))
            (Nat.le_add_right _ _)]
          rw [show (bunchedBimonoidIdentityMat (preTop + 1)).rows = preTop + 1 from rfl,
            show (bunchedBimonoidIdentityMat (preTop + 1)).cols = preTop + 1 from rfl]
          rw [bunchedBimonoidAddSubCancelLeft (preTop + 1) rowLocal,
            bunchedBimonoidAddSubCancelLeft (preTop + 1) colLocal]
          rw [bunchedBimonoidIdentityMatEntry (preBottom + 1) (rowLocal + 1) (colLocal + 1)
            (Nat.succ_lt_succ rowLocalBelow)
            (Nat.succ_lt_succ (Nat.lt_of_add_lt_add_left
              (show (preTop + 1) + colLocal < (preTop + 1) + preBottom from colBelow)))]
          rw [show ((rowLocal + 1) == (colLocal + 1)) = (rowLocal == colLocal) from
            bunchedBimonoidAugBeqShiftCancelRight rowLocal colLocal 1]
          rw [bunchedBimonoidAugBeqShiftCancelLeft (preTop + 1) rowLocal colLocal]

/-! # =========================================================================================
    # D4 — POINTED-TENSOR MULTIPLICATIVITY (the interchange/functoriality engine)
    # =========================================================================================
-/

/-- Successor transport below a predecessor bound. -/
theorem bunchedBimonoidAugSuccLtOfLtPred : (bound index : Nat) → index < Nat.pred bound →
    index + 1 < bound
  | 0, _, below => absurd below (Nat.not_lt_zero _)
  | _ + 1, _, below => Nat.succ_lt_succ below

/-- The `(x + 1) + y = x + (y + 1)` shuffle in the `+ 1` spelling. -/
theorem bunchedBimonoidAugSuccAddShuffle (leftValue rightValue : Nat) :
    (leftValue + 1) + rightValue = leftValue + (rightValue + 1) :=
  Nat.succ_add leftValue rightValue

/-- The wire-then-block index reshape `(t + 1) + pred r = t + r` for positive `r`. -/
theorem bunchedBimonoidAugWireBlockIndex (localIndex bound : Nat) (boundPos : 0 < bound) :
    (localIndex + 1) + Nat.pred bound = localIndex + bound := by
  rw [Nat.add_assoc localIndex 1 (Nat.pred bound), Nat.add_comm 1 (Nat.pred bound),
    bunchedBimonoidAugSuccPredOfPos bound boundPos]

/-- A bound in the `0 + (pred + 1)` spelling (the head-peel reshape). -/
theorem bunchedBimonoidAugHeadPeelShape (bound : Nat) (boundPos : 0 < bound) :
    bound = 0 + (Nat.pred bound + 1) := by
  rw [Nat.zero_add]
  exact (bunchedBimonoidAugSuccPredOfPos bound boundPos).symm

/-- ★★ **PT-multiplicativity, TOP-ROW entries** — on the rows of the top block the composite contraction
reproduces the `matMul blockA blockC` contraction (the bottom zone dies against the top row's pad). -/
theorem bunchedBimonoidAugPointedTensorMulTopEntry (blockA blockB blockC blockD : BunchedBimonoidMat)
    (topCompose : blockA.cols = blockC.rows)
    (headedC : bunchedBimonoidAugHeadedMat blockC)
    (rowsPosC : 0 < blockC.rows) (colsPosA : 0 < blockA.cols)
    (rowIndex colIndex : Nat) (rowInTop : rowIndex < blockA.rows)
    (colBelow : colIndex < blockC.cols + Nat.pred blockD.cols) :
    bunchedBimonoidMatEntryAt
        (bunchedBimonoidMatMul (bunchedBimonoidAugPointedTensor blockA blockB)
          (bunchedBimonoidAugPointedTensor blockC blockD)) rowIndex colIndex
      = bunchedBimonoidAugPointedTensorEntry (bunchedBimonoidMatMul blockA blockC)
          (bunchedBimonoidMatMul blockB blockD) rowIndex colIndex := by
  have rowBelowFull : rowIndex < blockA.rows + Nat.pred blockB.rows :=
    Nat.lt_of_lt_of_le rowInTop (Nat.le_add_right _ _)
  rw [bunchedBimonoidMatMulEntryRead (bunchedBimonoidAugPointedTensor blockA blockB)
    (bunchedBimonoidAugPointedTensor blockC blockD) rowIndex colIndex rowBelowFull colBelow]
  have sourceTerm : ∀ (contractionIndex : Nat),
      contractionIndex < blockC.rows + Nat.pred blockD.rows →
      bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockA blockB) rowIndex
          contractionIndex
        * bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD) contractionIndex
            colIndex
      = (if contractionIndex < blockC.rows then
          bunchedBimonoidMatEntryAt blockA rowIndex contractionIndex
            * bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD)
                contractionIndex colIndex
        else 0) := by
    intro contractionIndex conBelow
    match Nat.lt_or_ge contractionIndex blockC.rows with
    | Or.inl conInC =>
        rw [if_pos conInC]
        rw [bunchedBimonoidAugPointedTensorRead blockA blockB rowIndex contractionIndex rowBelowFull
          (Nat.lt_of_lt_of_le (topCompose ▸ conInC) (Nat.le_add_right _ _))]
        rw [bunchedBimonoidAugPointedTensorEntryTop blockA blockB rowIndex contractionIndex rowInTop
          (topCompose ▸ conInC)]
    | Or.inr conPastC =>
        rw [if_neg (fun conInC => Nat.lt_irrefl contractionIndex
          (Nat.lt_of_lt_of_le conInC conPastC))]
        have leftFactorZero : bunchedBimonoidMatEntryAt
            (bunchedBimonoidAugPointedTensor blockA blockB) rowIndex contractionIndex = 0 := by
          match Nat.lt_or_ge contractionIndex (blockA.cols + Nat.pred blockB.cols) with
          | Or.inl conInRange =>
              rw [bunchedBimonoidAugPointedTensorRead blockA blockB rowIndex contractionIndex
                rowBelowFull conInRange]
              exact bunchedBimonoidAugPointedTensorEntryTopPad blockA blockB rowIndex
                contractionIndex rowInTop (topCompose ▸ conPastC)
          | Or.inr conBeyond =>
              exact bunchedBimonoidAugEntryBeyondCol _
                (bunchedBimonoidAugPointedTensorWellFormed _ _) rowIndex contractionIndex conBeyond
        rw [leftFactorZero, bunchedBimonoidNatZeroMul]
  rw [show (bunchedBimonoidAugPointedTensor blockC blockD).rows
    = blockC.rows + Nat.pred blockD.rows from rfl]
  rw [congrArg bunchedBimonoidNatListSum
    (bunchedBimonoidRangeMapCongr _ _ (blockC.rows + Nat.pred blockD.rows) sourceTerm)]
  match Nat.lt_or_ge colIndex blockC.cols with
  | Or.inl colInTop =>
      rw [bunchedBimonoidAugPointedTensorEntryTop (bunchedBimonoidMatMul blockA blockC)
        (bunchedBimonoidMatMul blockB blockD) rowIndex colIndex rowInTop colInTop]
      rw [bunchedBimonoidMatMulEntryRead blockA blockC rowIndex colIndex rowInTop colInTop]
      rw [bunchedBimonoidNatListSumRangeAddSplit _ blockC.rows (Nat.pred blockD.rows)]
      have tailZero : bunchedBimonoidNatListSum ((List.range (Nat.pred blockD.rows)).map
          (fun tailIndex =>
            if tailIndex + blockC.rows < blockC.rows then
              bunchedBimonoidMatEntryAt blockA rowIndex (tailIndex + blockC.rows)
                * bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD)
                    (tailIndex + blockC.rows) colIndex
            else 0)) = 0 := by
        refine bunchedBimonoidAugSumRangeZero _ _ (fun tailIndex _ => ?_)
        rw [if_neg (fun bad => Nat.lt_irrefl blockC.rows
          (Nat.lt_of_le_of_lt (Nat.le_add_left blockC.rows tailIndex) bad))]
      rw [tailZero]
      have headMatch : ∀ (contractionIndex : Nat), contractionIndex < blockC.rows →
          (if contractionIndex < blockC.rows then
            bunchedBimonoidMatEntryAt blockA rowIndex contractionIndex
              * bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD)
                  contractionIndex colIndex
          else 0)
          = bunchedBimonoidMatEntryAt blockA rowIndex contractionIndex
              * bunchedBimonoidMatEntryAt blockC contractionIndex colIndex := by
        intro contractionIndex conInC
        rw [if_pos conInC]
        rw [bunchedBimonoidAugPointedTensorRead blockC blockD contractionIndex colIndex
          (Nat.lt_of_lt_of_le conInC (Nat.le_add_right _ _))
          (Nat.lt_of_lt_of_le colInTop (Nat.le_add_right _ _))]
        rw [bunchedBimonoidAugPointedTensorEntryTop blockC blockD contractionIndex colIndex conInC
          colInTop]
      rw [congrArg bunchedBimonoidNatListSum
        (bunchedBimonoidRangeMapCongr _ _ blockC.rows headMatch)]
      rfl
  | Or.inr colPastTop =>
      rw [bunchedBimonoidAugPointedTensorEntryTopPad (bunchedBimonoidMatMul blockA blockC)
        (bunchedBimonoidMatMul blockB blockD) rowIndex colIndex rowInTop colPastTop]
      refine bunchedBimonoidAugSumRangeZero _ _ (fun contractionIndex conBelow => ?_)
      match Nat.lt_or_ge contractionIndex blockC.rows with
      | Or.inl conInC =>
          rw [if_pos conInC]
          rw [bunchedBimonoidAugPointedTensorRead blockC blockD contractionIndex colIndex
            (Nat.lt_of_lt_of_le conInC (Nat.le_add_right _ _)) colBelow]
          rw [bunchedBimonoidAugPointedTensorEntryTopPad blockC blockD contractionIndex colIndex
            conInC colPastTop]
          rfl
      | Or.inr conPastC =>
          rw [if_neg (fun conInC => Nat.lt_irrefl contractionIndex
            (Nat.lt_of_lt_of_le conInC conPastC))]

/-- ★★ **PT-multiplicativity, BOTTOM-ROW entries** — on the rows of the bottom block the composite
contraction reproduces the `matMul blockB blockD` contraction: the point term matches the peeled head of the
bottom contraction (headedness), the wire zone dies, and the block zone matches the tail. -/
theorem bunchedBimonoidAugPointedTensorMulBottomEntry (blockA blockB blockC blockD : BunchedBimonoidMat)
    (topCompose : blockA.cols = blockC.rows)
    (headedC : bunchedBimonoidAugHeadedMat blockC) (headedD : bunchedBimonoidAugHeadedMat blockD)
    (rowsPosC : 0 < blockC.rows) (colsPosC : 0 < blockC.cols)
    (rowsPosD : 0 < blockD.rows) (colsPosD : 0 < blockD.cols)
    (colsPosB : 0 < blockB.cols) (wfB : bunchedBimonoidMatWellFormed blockB)
    (bottomLocal colIndex : Nat)
    (rowBelow : blockA.rows + bottomLocal < blockA.rows + Nat.pred blockB.rows)
    (colBelow : colIndex < blockC.cols + Nat.pred blockD.cols) :
    bunchedBimonoidMatEntryAt
        (bunchedBimonoidMatMul (bunchedBimonoidAugPointedTensor blockA blockB)
          (bunchedBimonoidAugPointedTensor blockC blockD)) (blockA.rows + bottomLocal) colIndex
      = bunchedBimonoidAugPointedTensorEntry (bunchedBimonoidMatMul blockA blockC)
          (bunchedBimonoidMatMul blockB blockD) (blockA.rows + bottomLocal) colIndex := by
  have colsPosA : 0 < blockA.cols := by rw [topCompose]; exact rowsPosC
  have rowPastTop : blockA.rows ≤ blockA.rows + bottomLocal := Nat.le_add_right _ _
  have bottomBelow : bottomLocal < Nat.pred blockB.rows := Nat.lt_of_add_lt_add_left rowBelow
  have bottomInB : bottomLocal + 1 < blockB.rows :=
    bunchedBimonoidAugSuccLtOfLtPred blockB.rows bottomLocal bottomBelow
  rw [bunchedBimonoidMatMulEntryRead (bunchedBimonoidAugPointedTensor blockA blockB)
    (bunchedBimonoidAugPointedTensor blockC blockD) (blockA.rows + bottomLocal) colIndex rowBelow
    colBelow]
  -- the three contraction zones
  rw [show (bunchedBimonoidAugPointedTensor blockC blockD).rows
    = blockC.rows + Nat.pred blockD.rows from rfl]
  rw [show blockC.rows + Nat.pred blockD.rows
      = Nat.pred blockC.rows + (Nat.pred blockD.rows + 1) from by
    rw [← bunchedBimonoidAugSuccPredOfPos blockC.rows rowsPosC,
      bunchedBimonoidAugSuccAddShuffle (Nat.pred blockC.rows) (Nat.pred blockD.rows)]
    rw [bunchedBimonoidAugSuccPredOfPos blockC.rows rowsPosC]]
  rw [bunchedBimonoidAugPointedContractionSplit _ (Nat.pred blockC.rows) (Nat.pred blockD.rows)]
  -- the point term
  have pointFactor : bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockA blockB)
      (blockA.rows + bottomLocal) 0 = bunchedBimonoidMatEntryAt blockB (bottomLocal + 1) 0 := by
    rw [bunchedBimonoidAugPointedTensorRead blockA blockB (blockA.rows + bottomLocal) 0 rowBelow
      (Nat.lt_of_lt_of_le colsPosA (Nat.le_add_right _ _))]
    rw [bunchedBimonoidAugPointedTensorEntryBottomOffset blockA blockB _ rowPastTop]
    rw [bunchedBimonoidAddSubCancelLeft blockA.rows bottomLocal]
  -- the wire zone dies
  have wireZero : ∀ (columnAt : Nat), bunchedBimonoidNatListSum ((List.range (Nat.pred blockC.rows)).map
      (fun wireIndex =>
        bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockA blockB)
            (blockA.rows + bottomLocal) (wireIndex + 1)
          * bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD) (wireIndex + 1)
              columnAt)) = 0 := by
    intro columnAt
    refine bunchedBimonoidAugSumRangeZero _ _ (fun wireIndex wireBelow => ?_)
    have wireInA : wireIndex + 1 < blockA.cols := by
      rw [topCompose]
      exact bunchedBimonoidAugSuccLtOfLtPred blockC.rows wireIndex wireBelow
    rw [bunchedBimonoidAugPointedTensorRead blockA blockB (blockA.rows + bottomLocal) (wireIndex + 1)
      rowBelow (Nat.lt_of_lt_of_le wireInA (Nat.le_add_right _ _))]
    rw [bunchedBimonoidAugPointedTensorEntryBottomZero blockA blockB _ (wireIndex + 1) rowPastTop
      (Nat.zero_lt_succ _) wireInA]
    rw [bunchedBimonoidNatZeroMul]
  -- the block zone reads B against the D-rows of the right factor
  have blockFactor : ∀ (blockIndex : Nat), blockIndex < Nat.pred blockD.rows →
      bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockA blockB)
          (blockA.rows + bottomLocal) ((blockIndex + 1) + Nat.pred blockC.rows)
        = bunchedBimonoidMatEntryAt blockB (bottomLocal + 1) (blockIndex + 1) := by
    intro blockIndex _
    rw [bunchedBimonoidAugWireBlockIndex blockIndex blockC.rows rowsPosC, ← topCompose]
    match Nat.lt_or_ge (blockIndex + blockA.cols) (blockA.cols + Nat.pred blockB.cols) with
    | Or.inl conInRange =>
        rw [bunchedBimonoidAugPointedTensorRead blockA blockB (blockA.rows + bottomLocal)
          (blockIndex + blockA.cols) rowBelow conInRange]
        rw [bunchedBimonoidAugPointedTensorEntryBottomBlock blockA blockB _ _ rowPastTop
          (Nat.lt_of_lt_of_le colsPosA (Nat.le_add_left blockA.cols blockIndex))
          (Nat.le_add_left blockA.cols blockIndex)]
        rw [bunchedBimonoidAddSubCancelLeft blockA.rows bottomLocal,
          bunchedBimonoidAddSubCancel blockIndex blockA.cols]
    | Or.inr conBeyond =>
        rw [bunchedBimonoidAugEntryBeyondCol _ (bunchedBimonoidAugPointedTensorWellFormed _ _)
          _ _ conBeyond]
        have blockIndexBeyond : Nat.pred blockB.cols ≤ blockIndex := by
          refine bunchedBimonoidAugLeOfAddLeAddLeft blockA.cols (Nat.pred blockB.cols) blockIndex ?_
          rw [Nat.add_comm blockA.cols blockIndex]
          exact conBeyond
        have colReadBeyond : blockB.cols ≤ blockIndex + 1 := by
          rw [← bunchedBimonoidAugSuccPredOfPos blockB.cols colsPosB]
          exact Nat.succ_le_succ blockIndexBeyond
        show (0 : Nat) = bunchedBimonoidMatEntryAt blockB (bottomLocal + 1) (blockIndex + 1)
        rw [bunchedBimonoidAugEntryBeyondCol blockB wfB (bottomLocal + 1) (blockIndex + 1)
          colReadBeyond]
  -- the right factor's block-zone reads
  have rightBlockRead : ∀ (blockIndex columnAt : Nat), blockIndex < Nat.pred blockD.rows →
      columnAt < blockC.cols + Nat.pred blockD.cols →
      bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD)
          ((blockIndex + 1) + Nat.pred blockC.rows) columnAt
        = bunchedBimonoidAugPointedTensorEntry blockC blockD (blockIndex + blockC.rows) columnAt := by
    intro blockIndex columnAt blockBelow columnBelow
    rw [bunchedBimonoidAugWireBlockIndex blockIndex blockC.rows rowsPosC]
    rw [bunchedBimonoidAugPointedTensorRead blockC blockD (blockIndex + blockC.rows) columnAt
      (by
        rw [Nat.add_comm blockIndex blockC.rows]
        exact Nat.add_lt_add_left blockBelow blockC.rows)
      columnBelow]
  -- split by the column zone
  match Nat.lt_or_ge colIndex blockC.cols with
  | Or.inl colInTop =>
      match colIndex, colInTop with
      | 0, _ =>
          -- offset column
          rw [bunchedBimonoidAugPointedTensorEntryBottomOffset (bunchedBimonoidMatMul blockA blockC)
            (bunchedBimonoidMatMul blockB blockD) _
            (show (bunchedBimonoidMatMul blockA blockC).rows ≤ blockA.rows + bottomLocal from
              rowPastTop)]
          rw [show (bunchedBimonoidMatMul blockA blockC).rows = blockA.rows from rfl]
          rw [bunchedBimonoidAddSubCancelLeft blockA.rows bottomLocal]
          rw [bunchedBimonoidMatMulEntryRead blockB blockD (bottomLocal + 1) 0 bottomInB colsPosD]
          conv =>
            rhs
            rw [bunchedBimonoidAugHeadPeelShape blockD.rows rowsPosD]
          rw [bunchedBimonoidAugPointedContractionSplit _ 0 (Nat.pred blockD.rows)]
          -- head: the B-offset against the D-header
          rw [pointFactor, wireZero 0]
          have sourcePoint : bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD)
              0 0 = 1 := by
            rw [bunchedBimonoidAugPointedTensorRead blockC blockD 0 0
              (Nat.lt_of_lt_of_le rowsPosC (Nat.le_add_right _ _))
              (Nat.lt_of_lt_of_le colsPosC (Nat.le_add_right _ _))]
            rw [bunchedBimonoidAugPointedTensorEntryTop blockC blockD 0 0 rowsPosC colsPosC]
            rw [headedC 0]
            rfl
          have targetPoint : bunchedBimonoidMatEntryAt blockD 0 0 = 1 := by
            rw [headedD 0]
            rfl
          rw [sourcePoint, targetPoint]
          have blockPiece : ∀ (blockIndex : Nat), blockIndex < Nat.pred blockD.rows →
              bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockA blockB)
                  (blockA.rows + bottomLocal) ((blockIndex + 1) + Nat.pred blockC.rows)
                * bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD)
                    ((blockIndex + 1) + Nat.pred blockC.rows) 0
              = bunchedBimonoidMatEntryAt blockB (bottomLocal + 1) ((blockIndex + 1) + 0)
                * bunchedBimonoidMatEntryAt blockD ((blockIndex + 1) + 0) 0 := by
            intro blockIndex blockBelow
            rw [blockFactor blockIndex blockBelow,
              rightBlockRead blockIndex 0 blockBelow
                (Nat.lt_of_lt_of_le colsPosC (Nat.le_add_right _ _))]
            rw [bunchedBimonoidAugPointedTensorEntryBottomOffset blockC blockD
              (blockIndex + blockC.rows) (Nat.le_add_left blockC.rows blockIndex)]
            rw [bunchedBimonoidAddSubCancel blockIndex blockC.rows]
          rw [congrArg bunchedBimonoidNatListSum
            (bunchedBimonoidRangeMapCongr _ _ (Nat.pred blockD.rows) blockPiece)]
          rw [bunchedBimonoidAugSumRangeZero 0 _ (fun _ below => absurd below (Nat.not_lt_zero _))]
      | colPos + 1, colInTopPos =>
          -- wire column: everything dies
          rw [bunchedBimonoidAugPointedTensorEntryBottomZero (bunchedBimonoidMatMul blockA blockC)
            (bunchedBimonoidMatMul blockB blockD) _ (colPos + 1)
            (show (bunchedBimonoidMatMul blockA blockC).rows ≤ blockA.rows + bottomLocal from
              rowPastTop)
            (Nat.zero_lt_succ _) colInTopPos]
          have pointDies : bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockA blockB)
              (blockA.rows + bottomLocal) 0
                * bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD) 0
                    (colPos + 1) = 0 := by
            rw [bunchedBimonoidAugPointedTensorRead blockC blockD 0 (colPos + 1)
              (Nat.lt_of_lt_of_le rowsPosC (Nat.le_add_right _ _)) colBelow]
            rw [bunchedBimonoidAugPointedTensorEntryTop blockC blockD 0 (colPos + 1) rowsPosC
              colInTopPos]
            rw [headedC (colPos + 1)]
            rfl
          have blockDies : bunchedBimonoidNatListSum ((List.range (Nat.pred blockD.rows)).map
              (fun blockIndex =>
                bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockA blockB)
                    (blockA.rows + bottomLocal) ((blockIndex + 1) + Nat.pred blockC.rows)
                  * bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD)
                      ((blockIndex + 1) + Nat.pred blockC.rows) (colPos + 1))) = 0 := by
            refine bunchedBimonoidAugSumRangeZero _ _ (fun blockIndex blockBelow => ?_)
            rw [rightBlockRead blockIndex (colPos + 1) blockBelow
              (Nat.lt_of_lt_of_le colInTopPos (Nat.le_add_right _ _))]
            rw [bunchedBimonoidAugPointedTensorEntryBottomZero blockC blockD
              (blockIndex + blockC.rows) (colPos + 1) (Nat.le_add_left blockC.rows blockIndex)
              (Nat.zero_lt_succ _) colInTopPos]
            rfl
          rw [pointDies, wireZero (colPos + 1), blockDies]
  | Or.inr colPastTop =>
      match Nat.le.dest colPastTop with
      | ⟨colLocal, colSplit⟩ =>
          have colShape : colIndex = blockC.cols + colLocal := colSplit.symm
          cases colShape
          have colLocalBelow : colLocal < Nat.pred blockD.cols :=
            Nat.lt_of_add_lt_add_left colBelow
          have colLocalInD : colLocal + 1 < blockD.cols :=
            bunchedBimonoidAugSuccLtOfLtPred blockD.cols colLocal colLocalBelow
          have colPosHere : 0 < blockC.cols + colLocal :=
            Nat.lt_of_lt_of_le colsPosC (Nat.le_add_right _ _)
          rw [bunchedBimonoidAugPointedTensorEntryBottomBlock (bunchedBimonoidMatMul blockA blockC)
            (bunchedBimonoidMatMul blockB blockD) _ _
            (show (bunchedBimonoidMatMul blockA blockC).rows ≤ blockA.rows + bottomLocal from
              rowPastTop)
            colPosHere
            (show (bunchedBimonoidMatMul blockA blockC).cols ≤ blockC.cols + colLocal from
              Nat.le_add_right _ _)]
          rw [show (bunchedBimonoidMatMul blockA blockC).rows = blockA.rows from rfl,
            show (bunchedBimonoidMatMul blockA blockC).cols = blockC.cols from rfl]
          rw [bunchedBimonoidAddSubCancelLeft blockA.rows bottomLocal,
            bunchedBimonoidAddSubCancelLeft blockC.cols colLocal]
          rw [bunchedBimonoidMatMulEntryRead blockB blockD (bottomLocal + 1) (colLocal + 1)
            bottomInB colLocalInD]
          conv =>
            rhs
            rw [bunchedBimonoidAugHeadPeelShape blockD.rows rowsPosD]
          rw [bunchedBimonoidAugPointedContractionSplit _ 0 (Nat.pred blockD.rows)]
          -- the peeled head dies against the D-header
          have targetHead : bunchedBimonoidMatEntryAt blockB (bottomLocal + 1) 0
              * bunchedBimonoidMatEntryAt blockD 0 (colLocal + 1) = 0 := by
            rw [headedD (colLocal + 1)]
            rfl
          have sourceHead : bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockA blockB)
              (blockA.rows + bottomLocal) 0
                * bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD) 0
                    (blockC.cols + colLocal) = 0 := by
            rw [bunchedBimonoidAugPointedTensorRead blockC blockD 0 (blockC.cols + colLocal)
              (Nat.lt_of_lt_of_le rowsPosC (Nat.le_add_right _ _)) colBelow]
            rw [bunchedBimonoidAugPointedTensorEntryTopPad blockC blockD 0 (blockC.cols + colLocal)
              rowsPosC (Nat.le_add_right _ _)]
            rfl
          rw [sourceHead, targetHead, wireZero (blockC.cols + colLocal)]
          have blockPiece : ∀ (blockIndex : Nat), blockIndex < Nat.pred blockD.rows →
              bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockA blockB)
                  (blockA.rows + bottomLocal) ((blockIndex + 1) + Nat.pred blockC.rows)
                * bunchedBimonoidMatEntryAt (bunchedBimonoidAugPointedTensor blockC blockD)
                    ((blockIndex + 1) + Nat.pred blockC.rows) (blockC.cols + colLocal)
              = bunchedBimonoidMatEntryAt blockB (bottomLocal + 1) ((blockIndex + 1) + 0)
                * bunchedBimonoidMatEntryAt blockD ((blockIndex + 1) + 0) (colLocal + 1) := by
            intro blockIndex blockBelow
            rw [blockFactor blockIndex blockBelow,
              rightBlockRead blockIndex (blockC.cols + colLocal) blockBelow colBelow]
            rw [bunchedBimonoidAugPointedTensorEntryBottomBlock blockC blockD
              (blockIndex + blockC.rows) (blockC.cols + colLocal)
              (Nat.le_add_left blockC.rows blockIndex) colPosHere (Nat.le_add_right _ _)]
            rw [bunchedBimonoidAddSubCancel blockIndex blockC.rows,
              bunchedBimonoidAddSubCancelLeft blockC.cols colLocal]
          rw [congrArg bunchedBimonoidNatListSum
            (bunchedBimonoidRangeMapCongr _ _ (Nat.pred blockD.rows) blockPiece)]
          rw [bunchedBimonoidAugSumRangeZero 0 _ (fun _ below => absurd below (Nat.not_lt_zero _))]

/-- ★★★ **POINTED-TENSOR MULTIPLICATIVITY** — `matMul (PT A B) (PT C D) = PT (matMul A C) (matMul B D)`
whenever the TOP pair is interface-composable, the right factors are headed with positive dimensions, and
`B` is well-formed with positive columns.  The single engine behind whisker-functoriality (both sides) and
the Godement interchange in the augmented semantics. -/
theorem bunchedBimonoidAugPointedTensorMul (blockA blockB blockC blockD : BunchedBimonoidMat)
    (topCompose : blockA.cols = blockC.rows)
    (headedC : bunchedBimonoidAugHeadedMat blockC) (headedD : bunchedBimonoidAugHeadedMat blockD)
    (rowsPosC : 0 < blockC.rows) (colsPosC : 0 < blockC.cols)
    (rowsPosD : 0 < blockD.rows) (colsPosD : 0 < blockD.cols)
    (colsPosB : 0 < blockB.cols) (wfB : bunchedBimonoidMatWellFormed blockB) :
    bunchedBimonoidMatMul (bunchedBimonoidAugPointedTensor blockA blockB)
        (bunchedBimonoidAugPointedTensor blockC blockD)
      = bunchedBimonoidAugPointedTensor (bunchedBimonoidMatMul blockA blockC)
          (bunchedBimonoidMatMul blockB blockD) := by
  refine bunchedBimonoidAugMatEqOfPointwise _ _ rfl rfl
    (bunchedBimonoidAugMatMulWellFormed _ _) (bunchedBimonoidAugPointedTensorWellFormed _ _)
    (fun rowIndex colIndex rowBelow colBelow => ?_)
  have colBelowShaped : colIndex < blockC.cols + Nat.pred blockD.cols := colBelow
  rw [show bunchedBimonoidMatEntryAt
      (bunchedBimonoidAugPointedTensor (bunchedBimonoidMatMul blockA blockC)
        (bunchedBimonoidMatMul blockB blockD)) rowIndex colIndex
    = bunchedBimonoidAugPointedTensorEntry (bunchedBimonoidMatMul blockA blockC)
        (bunchedBimonoidMatMul blockB blockD) rowIndex colIndex from
    bunchedBimonoidAugPointedTensorRead _ _ rowIndex colIndex rowBelow colBelow]
  match bunchedBimonoidAugIndexSplit blockA.rows rowIndex with
  | Or.inl rowInTop =>
      exact bunchedBimonoidAugPointedTensorMulTopEntry blockA blockB blockC blockD topCompose
        headedC rowsPosC (by rw [topCompose]; exact rowsPosC) rowIndex colIndex rowInTop
        colBelowShaped
  | Or.inr ⟨bottomLocal, rowEq⟩ =>
      cases rowEq
      exact bunchedBimonoidAugPointedTensorMulBottomEntry blockA blockB blockC blockD topCompose
        headedC headedD rowsPosC colsPosC rowsPosD colsPosD colsPosB wfB bottomLocal colIndex
        rowBelow colBelowShaped

/-! # =========================================================================================
    # D5 — POINTED-TENSOR ASSOCIATIVITY (the whisker-associator engine)
    # =========================================================================================
-/

/-- The nested block-local subtraction `((base + local) + 1) - (base + 1) = local`. -/
theorem bunchedBimonoidAugShiftSubOne (base localValue : Nat) :
    ((base + localValue) + 1) - (base + 1) = localValue := by
  rw [show (base + localValue) + 1 = (base + 1) + localValue from (Nat.succ_add base localValue).symm]
  exact bunchedBimonoidAddSubCancelLeft (base + 1) localValue

/-- ★★★ **POINTED-TENSOR ASSOCIATIVITY** — `PT A (PT B C) = PT (PT A B) C` (positive middle dimensions and
positive top columns). -/
theorem bunchedBimonoidAugPointedTensorAssoc (blockA blockB blockC : BunchedBimonoidMat)
    (rowsPosB : 0 < blockB.rows) (colsPosB : 0 < blockB.cols) (colsPosA : 0 < blockA.cols) :
    bunchedBimonoidAugPointedTensor blockA (bunchedBimonoidAugPointedTensor blockB blockC)
      = bunchedBimonoidAugPointedTensor (bunchedBimonoidAugPointedTensor blockA blockB) blockC := by
  have rowsEq : blockA.rows + Nat.pred (blockB.rows + Nat.pred blockC.rows)
      = (blockA.rows + Nat.pred blockB.rows) + Nat.pred blockC.rows := by
    rw [← bunchedBimonoidAugSuccPredOfPos blockB.rows rowsPosB,
      bunchedBimonoidAugSuccAddShuffle (Nat.pred blockB.rows) (Nat.pred blockC.rows)]
    exact (Nat.add_assoc blockA.rows (Nat.pred blockB.rows) (Nat.pred blockC.rows)).symm
  have colsEq : blockA.cols + Nat.pred (blockB.cols + Nat.pred blockC.cols)
      = (blockA.cols + Nat.pred blockB.cols) + Nat.pred blockC.cols := by
    rw [← bunchedBimonoidAugSuccPredOfPos blockB.cols colsPosB,
      bunchedBimonoidAugSuccAddShuffle (Nat.pred blockB.cols) (Nat.pred blockC.cols)]
    exact (Nat.add_assoc blockA.cols (Nat.pred blockB.cols) (Nat.pred blockC.cols)).symm
  refine bunchedBimonoidAugMatEqOfPointwise _ _
    (show blockA.rows + Nat.pred ((bunchedBimonoidAugPointedTensor blockB blockC).rows)
        = ((bunchedBimonoidAugPointedTensor blockA blockB).rows) + Nat.pred blockC.rows
      from rowsEq)
    (show blockA.cols + Nat.pred ((bunchedBimonoidAugPointedTensor blockB blockC).cols)
        = ((bunchedBimonoidAugPointedTensor blockA blockB).cols) + Nat.pred blockC.cols
      from colsEq)
    (bunchedBimonoidAugPointedTensorWellFormed _ _) (bunchedBimonoidAugPointedTensorWellFormed _ _)
    (fun rowIndex colIndex rowBelow colBelow => ?_)
  rw [bunchedBimonoidAugPointedTensorRead blockA (bunchedBimonoidAugPointedTensor blockB blockC)
    rowIndex colIndex rowBelow colBelow]
  rw [bunchedBimonoidAugPointedTensorRead (bunchedBimonoidAugPointedTensor blockA blockB) blockC
    rowIndex colIndex (rowsEq ▸ rowBelow) (colsEq ▸ colBelow)]
  match bunchedBimonoidAugIndexSplit blockA.rows rowIndex with
  | Or.inl rowInA =>
      -- ================= A-ROWS =================
      have rowInOuter : rowIndex < (bunchedBimonoidAugPointedTensor blockA blockB).rows :=
        Nat.lt_of_lt_of_le rowInA (Nat.le_add_right _ _)
      match bunchedBimonoidAugIndexSplit blockA.cols colIndex with
      | Or.inl colInA =>
          rw [bunchedBimonoidAugPointedTensorEntryTop blockA
            (bunchedBimonoidAugPointedTensor blockB blockC) rowIndex colIndex rowInA colInA]
          rw [bunchedBimonoidAugPointedTensorEntryTop (bunchedBimonoidAugPointedTensor blockA blockB)
            blockC rowIndex colIndex rowInOuter
            (Nat.lt_of_lt_of_le colInA (Nat.le_add_right _ _))]
          rw [bunchedBimonoidAugPointedTensorRead blockA blockB rowIndex colIndex rowInOuter
            (Nat.lt_of_lt_of_le colInA (Nat.le_add_right _ _))]
          rw [bunchedBimonoidAugPointedTensorEntryTop blockA blockB rowIndex colIndex rowInA colInA]
      | Or.inr ⟨colLocal, colEq⟩ =>
          cases colEq
          rw [bunchedBimonoidAugPointedTensorEntryTopPad blockA
            (bunchedBimonoidAugPointedTensor blockB blockC) rowIndex _ rowInA (Nat.le_add_right _ _)]
          match Nat.lt_or_ge (blockA.cols + colLocal)
            (blockA.cols + Nat.pred blockB.cols) with
          | Or.inl colInOuter =>
              rw [bunchedBimonoidAugPointedTensorEntryTop
                (bunchedBimonoidAugPointedTensor blockA blockB) blockC rowIndex _ rowInOuter
                colInOuter]
              rw [bunchedBimonoidAugPointedTensorRead blockA blockB rowIndex _ rowInOuter colInOuter]
              rw [bunchedBimonoidAugPointedTensorEntryTopPad blockA blockB rowIndex _ rowInA
                (Nat.le_add_right _ _)]
          | Or.inr colPastOuter =>
              rw [bunchedBimonoidAugPointedTensorEntryTopPad
                (bunchedBimonoidAugPointedTensor blockA blockB) blockC rowIndex _ rowInOuter
                colPastOuter]
  | Or.inr ⟨rowLocal, rowEq⟩ =>
      cases rowEq
      have rowPastA : blockA.rows ≤ blockA.rows + rowLocal := Nat.le_add_right _ _
      have rowLocalBelow : rowLocal < Nat.pred (blockB.rows + Nat.pred blockC.rows) :=
        Nat.lt_of_add_lt_add_left (n := blockA.rows) rowBelow
      have innerRowBelow : rowLocal + 1 < blockB.rows + Nat.pred blockC.rows :=
        bunchedBimonoidAugSuccLtOfLtPred (blockB.rows + Nat.pred blockC.rows) rowLocal rowLocalBelow
      match bunchedBimonoidAugIndexSplit (Nat.pred blockB.rows) rowLocal with
      | Or.inl rowInB =>
          -- ================= B-ROWS =================
          have rowLocalInB : rowLocal + 1 < blockB.rows :=
            bunchedBimonoidAugSuccLtOfLtPred blockB.rows rowLocal rowInB
          have rowInOuter : blockA.rows + rowLocal
              < (bunchedBimonoidAugPointedTensor blockA blockB).rows :=
            Nat.add_lt_add_left rowInB blockA.rows
          match bunchedBimonoidAugIndexSplit blockA.cols colIndex with
          | Or.inl colInA =>
              match colIndex, colInA with
              | 0, _ =>
                  rw [bunchedBimonoidAugPointedTensorEntryBottomOffset blockA
                    (bunchedBimonoidAugPointedTensor blockB blockC) _ rowPastA]
                  rw [bunchedBimonoidAddSubCancelLeft blockA.rows rowLocal]
                  rw [bunchedBimonoidAugPointedTensorRead blockB blockC (rowLocal + 1) 0
                    innerRowBelow (Nat.lt_of_lt_of_le colsPosB (Nat.le_add_right _ _))]
                  rw [bunchedBimonoidAugPointedTensorEntryTop blockB blockC (rowLocal + 1) 0
                    rowLocalInB colsPosB]
                  rw [bunchedBimonoidAugPointedTensorEntryTop
                    (bunchedBimonoidAugPointedTensor blockA blockB) blockC _ 0 rowInOuter
                    (Nat.lt_of_lt_of_le colsPosA (Nat.le_add_right _ _))]
                  rw [bunchedBimonoidAugPointedTensorRead blockA blockB _ 0 rowInOuter
                    (Nat.lt_of_lt_of_le colsPosA (Nat.le_add_right _ _))]
                  rw [bunchedBimonoidAugPointedTensorEntryBottomOffset blockA blockB _ rowPastA]
                  rw [bunchedBimonoidAddSubCancelLeft blockA.rows rowLocal]
              | colPos + 1, colInAPos =>
                  rw [bunchedBimonoidAugPointedTensorEntryBottomZero blockA
                    (bunchedBimonoidAugPointedTensor blockB blockC) _ (colPos + 1) rowPastA
                    (Nat.zero_lt_succ _) colInAPos]
                  rw [bunchedBimonoidAugPointedTensorEntryTop
                    (bunchedBimonoidAugPointedTensor blockA blockB) blockC _ (colPos + 1) rowInOuter
                    (Nat.lt_of_lt_of_le colInAPos (Nat.le_add_right _ _))]
                  rw [bunchedBimonoidAugPointedTensorRead blockA blockB _ (colPos + 1) rowInOuter
                    (Nat.lt_of_lt_of_le colInAPos (Nat.le_add_right _ _))]
                  rw [bunchedBimonoidAugPointedTensorEntryBottomZero blockA blockB _ (colPos + 1)
                    rowPastA (Nat.zero_lt_succ _) colInAPos]
          | Or.inr ⟨colLocal, colEq⟩ =>
              cases colEq
              have colPosGlobal : 0 < blockA.cols + colLocal :=
                Nat.lt_of_lt_of_le colsPosA (Nat.le_add_right _ _)
              rw [bunchedBimonoidAugPointedTensorEntryBottomBlock blockA
                (bunchedBimonoidAugPointedTensor blockB blockC) _ _ rowPastA colPosGlobal
                (Nat.le_add_right _ _)]
              rw [bunchedBimonoidAddSubCancelLeft blockA.rows rowLocal,
                bunchedBimonoidAddSubCancelLeft blockA.cols colLocal]
              match bunchedBimonoidAugIndexSplit (Nat.pred blockB.cols) colLocal with
              | Or.inl colInB =>
                  have colLocalInB : colLocal + 1 < blockB.cols :=
                    bunchedBimonoidAugSuccLtOfLtPred blockB.cols colLocal colInB
                  have colInOuter : blockA.cols + colLocal
                      < (bunchedBimonoidAugPointedTensor blockA blockB).cols :=
                    Nat.add_lt_add_left colInB blockA.cols
                  rw [bunchedBimonoidAugPointedTensorRead blockB blockC (rowLocal + 1) (colLocal + 1)
                    innerRowBelow (Nat.lt_of_lt_of_le colLocalInB (Nat.le_add_right _ _))]
                  rw [bunchedBimonoidAugPointedTensorEntryTop blockB blockC (rowLocal + 1)
                    (colLocal + 1) rowLocalInB colLocalInB]
                  rw [bunchedBimonoidAugPointedTensorEntryTop
                    (bunchedBimonoidAugPointedTensor blockA blockB) blockC _ _ rowInOuter colInOuter]
                  rw [bunchedBimonoidAugPointedTensorRead blockA blockB _ _ rowInOuter colInOuter]
                  rw [bunchedBimonoidAugPointedTensorEntryBottomBlock blockA blockB _ _ rowPastA
                    colPosGlobal (Nat.le_add_right _ _)]
                  rw [bunchedBimonoidAddSubCancelLeft blockA.rows rowLocal,
                    bunchedBimonoidAddSubCancelLeft blockA.cols colLocal]
              | Or.inr ⟨colFar, colFarEq⟩ =>
                  cases colFarEq
                  have colReadBeyond : blockB.cols ≤ (Nat.pred blockB.cols + colFar) + 1 := by
                    rw [← bunchedBimonoidAugSuccPredOfPos blockB.cols colsPosB]
                    exact Nat.succ_le_succ (Nat.le_add_right _ _)
                  have colReadBelow : (Nat.pred blockB.cols + colFar) + 1
                      < blockB.cols + Nat.pred blockC.cols :=
                    bunchedBimonoidAugSuccLtOfLtPred (blockB.cols + Nat.pred blockC.cols) _
                      (Nat.lt_of_add_lt_add_left (n := blockA.cols) colBelow)
                  rw [bunchedBimonoidAugPointedTensorRead blockB blockC (rowLocal + 1)
                    ((Nat.pred blockB.cols + colFar) + 1) innerRowBelow colReadBelow]
                  rw [bunchedBimonoidAugPointedTensorEntryTopPad blockB blockC (rowLocal + 1)
                    ((Nat.pred blockB.cols + colFar) + 1) rowLocalInB colReadBeyond]
                  have colPastOuter : (bunchedBimonoidAugPointedTensor blockA blockB).cols
                      ≤ blockA.cols + (Nat.pred blockB.cols + colFar) := by
                    rw [show (bunchedBimonoidAugPointedTensor blockA blockB).cols
                      = blockA.cols + Nat.pred blockB.cols from rfl]
                    rw [← Nat.add_assoc blockA.cols (Nat.pred blockB.cols) colFar]
                    exact Nat.le_add_right _ _
                  rw [bunchedBimonoidAugPointedTensorEntryTopPad
                    (bunchedBimonoidAugPointedTensor blockA blockB) blockC _ _ rowInOuter
                    colPastOuter]
      | Or.inr ⟨rowFar, rowFarEq⟩ =>
          -- ================= C-ROWS =================
          cases rowFarEq
          have rowPastOuter : (bunchedBimonoidAugPointedTensor blockA blockB).rows
              ≤ blockA.rows + (Nat.pred blockB.rows + rowFar) := by
            rw [show (bunchedBimonoidAugPointedTensor blockA blockB).rows
              = blockA.rows + Nat.pred blockB.rows from rfl]
            rw [← Nat.add_assoc blockA.rows (Nat.pred blockB.rows) rowFar]
            exact Nat.le_add_right _ _
          have rowPastB : blockB.rows ≤ (Nat.pred blockB.rows + rowFar) + 1 := by
            rw [← bunchedBimonoidAugSuccPredOfPos blockB.rows rowsPosB]
            exact Nat.succ_le_succ (Nat.le_add_right _ _)
          have outerBottomLocal : blockA.rows + (Nat.pred blockB.rows + rowFar)
              - (bunchedBimonoidAugPointedTensor blockA blockB).rows = rowFar := by
            rw [show (bunchedBimonoidAugPointedTensor blockA blockB).rows
              = blockA.rows + Nat.pred blockB.rows from rfl]
            rw [← Nat.add_assoc blockA.rows (Nat.pred blockB.rows) rowFar]
            exact bunchedBimonoidAddSubCancelLeft (blockA.rows + Nat.pred blockB.rows) rowFar
          have innerBottomLocal : ((Nat.pred blockB.rows + rowFar) + 1) - blockB.rows = rowFar := by
            rw [← bunchedBimonoidAugSuccPredOfPos blockB.rows rowsPosB]
            exact bunchedBimonoidAugShiftSubOne (Nat.pred blockB.rows) rowFar
          match bunchedBimonoidAugIndexSplit blockA.cols colIndex with
          | Or.inl colInA =>
              match colIndex, colInA with
              | 0, _ =>
                  rw [bunchedBimonoidAugPointedTensorEntryBottomOffset blockA
                    (bunchedBimonoidAugPointedTensor blockB blockC) _ rowPastA]
                  rw [bunchedBimonoidAddSubCancelLeft blockA.rows (Nat.pred blockB.rows + rowFar)]
                  rw [bunchedBimonoidAugPointedTensorRead blockB blockC _ 0 innerRowBelow
                    (Nat.lt_of_lt_of_le colsPosB (Nat.le_add_right _ _))]
                  rw [bunchedBimonoidAugPointedTensorEntryBottomOffset blockB blockC _ rowPastB]
                  rw [innerBottomLocal]
                  rw [bunchedBimonoidAugPointedTensorEntryBottomOffset
                    (bunchedBimonoidAugPointedTensor blockA blockB) blockC _ rowPastOuter]
                  rw [outerBottomLocal]
              | colPos + 1, colInAPos =>
                  rw [bunchedBimonoidAugPointedTensorEntryBottomZero blockA
                    (bunchedBimonoidAugPointedTensor blockB blockC) _ (colPos + 1) rowPastA
                    (Nat.zero_lt_succ _) colInAPos]
                  rw [bunchedBimonoidAugPointedTensorEntryBottomZero
                    (bunchedBimonoidAugPointedTensor blockA blockB) blockC _ (colPos + 1)
                    rowPastOuter (Nat.zero_lt_succ _)
                    (Nat.lt_of_lt_of_le colInAPos (Nat.le_add_right _ _))]
          | Or.inr ⟨colLocal, colEq⟩ =>
              cases colEq
              have colPosGlobal : 0 < blockA.cols + colLocal :=
                Nat.lt_of_lt_of_le colsPosA (Nat.le_add_right _ _)
              rw [bunchedBimonoidAugPointedTensorEntryBottomBlock blockA
                (bunchedBimonoidAugPointedTensor blockB blockC) _ _ rowPastA colPosGlobal
                (Nat.le_add_right _ _)]
              rw [bunchedBimonoidAddSubCancelLeft blockA.rows (Nat.pred blockB.rows + rowFar),
                bunchedBimonoidAddSubCancelLeft blockA.cols colLocal]
              match bunchedBimonoidAugIndexSplit (Nat.pred blockB.cols) colLocal with
              | Or.inl colInB =>
                  have colLocalInB : colLocal + 1 < blockB.cols :=
                    bunchedBimonoidAugSuccLtOfLtPred blockB.cols colLocal colInB
                  have colInOuter : blockA.cols + colLocal
                      < (bunchedBimonoidAugPointedTensor blockA blockB).cols :=
                    Nat.add_lt_add_left colInB blockA.cols
                  rw [bunchedBimonoidAugPointedTensorRead blockB blockC _ (colLocal + 1)
                    innerRowBelow (Nat.lt_of_lt_of_le colLocalInB (Nat.le_add_right _ _))]
                  rw [bunchedBimonoidAugPointedTensorEntryBottomZero blockB blockC _ (colLocal + 1)
                    rowPastB (Nat.zero_lt_succ _) colLocalInB]
                  rw [bunchedBimonoidAugPointedTensorEntryBottomZero
                    (bunchedBimonoidAugPointedTensor blockA blockB) blockC _ _ rowPastOuter
                    colPosGlobal colInOuter]
              | Or.inr ⟨colFar, colFarEq⟩ =>
                  cases colFarEq
                  have colReadBeyond : blockB.cols ≤ (Nat.pred blockB.cols + colFar) + 1 := by
                    rw [← bunchedBimonoidAugSuccPredOfPos blockB.cols colsPosB]
                    exact Nat.succ_le_succ (Nat.le_add_right _ _)
                  have colReadBelow : (Nat.pred blockB.cols + colFar) + 1
                      < blockB.cols + Nat.pred blockC.cols :=
                    bunchedBimonoidAugSuccLtOfLtPred (blockB.cols + Nat.pred blockC.cols) _
                      (Nat.lt_of_add_lt_add_left (n := blockA.cols) colBelow)
                  have innerBottomColLocal : ((Nat.pred blockB.cols + colFar) + 1) - blockB.cols
                      = colFar := by
                    rw [← bunchedBimonoidAugSuccPredOfPos blockB.cols colsPosB]
                    exact bunchedBimonoidAugShiftSubOne (Nat.pred blockB.cols) colFar
                  have colPastOuter : (bunchedBimonoidAugPointedTensor blockA blockB).cols
                      ≤ blockA.cols + (Nat.pred blockB.cols + colFar) := by
                    rw [show (bunchedBimonoidAugPointedTensor blockA blockB).cols
                      = blockA.cols + Nat.pred blockB.cols from rfl]
                    rw [← Nat.add_assoc blockA.cols (Nat.pred blockB.cols) colFar]
                    exact Nat.le_add_right _ _
                  have outerBottomColLocal : blockA.cols + (Nat.pred blockB.cols + colFar)
                      - (bunchedBimonoidAugPointedTensor blockA blockB).cols = colFar := by
                    rw [show (bunchedBimonoidAugPointedTensor blockA blockB).cols
                      = blockA.cols + Nat.pred blockB.cols from rfl]
                    rw [← Nat.add_assoc blockA.cols (Nat.pred blockB.cols) colFar]
                    exact bunchedBimonoidAddSubCancelLeft (blockA.cols + Nat.pred blockB.cols) colFar
                  rw [bunchedBimonoidAugPointedTensorRead blockB blockC _ _ innerRowBelow
                    colReadBelow]
                  rw [bunchedBimonoidAugPointedTensorEntryBottomBlock blockB blockC _ _ rowPastB
                    (Nat.lt_of_lt_of_le colsPosB colReadBeyond) colReadBeyond]
                  rw [innerBottomLocal, innerBottomColLocal]
                  rw [bunchedBimonoidAugPointedTensorEntryBottomBlock
                    (bunchedBimonoidAugPointedTensor blockA blockB) blockC _ _ rowPastOuter
                    colPosGlobal colPastOuter]
                  rw [outerBottomLocal, outerBottomColLocal]

/-! # =========================================================================================
    # E — THE COMPOSABILITY-GATED ABSORBER over the FULL star scope
    # =========================================================================================
-/

/-- ★ **The dimension-gated Clean predicate** — the composability fold matters exactly at dimension 2 (where
the augmented matrices live); every other dimension is ungated.  This dodges the boundary-recomputation
non-closure of a naive all-dimension gate under the higher-dimensional strict unit rows. -/
def bunchedBimonoidAugCleanGate : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Bool
  | 0, _ => true
  | 1, _ => true
  | 2, cell => bunchedBimonoidAugCleanCell cell
  | _ + 3, _ => true

/-- ★★ **The gated augmented-equality relation** — Clean-equivalence plus augmented-value equality GIVEN
Clean.  The target relation the star scope's saturated congruence folds into. -/
def bunchedBimonoidAugGatedEq : CellRelOver bunchedBimonoidOmegaComputad :=
  fun {_dim} cellAlpha cellBeta =>
    (bunchedBimonoidAugCleanGate cellAlpha = true ↔ bunchedBimonoidAugCleanGate cellBeta = true)
      ∧ (bunchedBimonoidAugCleanGate cellAlpha = true → bunchedBimonoidAugCleanGate cellBeta = true →
        bunchedBimonoidEvalAugCell cellAlpha = bunchedBimonoidEvalAugCell cellBeta)

/-! ## The eleven strict rows, absorbed -/

/-- vcompAssoc is absorbed. -/
theorem bunchedBimonoidAugGatedVcompAssoc {dim : Nat}
    (cellA cellB cellC : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidAugGatedEq
      (CellExpr.vcomp (CellExpr.vcomp cellA cellB) cellC)
      (CellExpr.vcomp cellA (CellExpr.vcomp cellB cellC)) := by
  match dim with
  | 0 =>
      exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ =>
        Nat.add_assoc (bunchedBimonoidEvalAugCell cellA) (bunchedBimonoidEvalAugCell cellB)
          (bunchedBimonoidEvalAugCell cellC)⟩
  | 1 =>
      refine ⟨Iff.intro (fun cleanLeft => ?_) (fun cleanRight => ?_), fun cleanLeft _ => ?_⟩
      · match bunchedBimonoidAugAndSplit cleanLeft with
        | ⟨cleanAB, restLeft⟩ =>
            match bunchedBimonoidAugAndSplit restLeft, bunchedBimonoidAugAndSplit cleanAB with
            | ⟨cleanC, composeABC⟩, ⟨cleanA, restAB⟩ =>
                match bunchedBimonoidAugAndSplit restAB with
                | ⟨cleanB, composeAB⟩ =>
                    exact bunchedBimonoidAugAndJoin cleanA
                      (bunchedBimonoidAugAndJoin
                        (bunchedBimonoidAugAndJoin cleanB
                          (bunchedBimonoidAugAndJoin cleanC composeABC))
                        composeAB)
      · match bunchedBimonoidAugAndSplit cleanRight with
        | ⟨cleanA, restRight⟩ =>
            match bunchedBimonoidAugAndSplit restRight with
            | ⟨cleanBC, composeABC⟩ =>
                match bunchedBimonoidAugAndSplit cleanBC with
                | ⟨cleanB, restBC⟩ =>
                    match bunchedBimonoidAugAndSplit restBC with
                    | ⟨cleanC, composeBC⟩ =>
                        exact bunchedBimonoidAugAndJoin
                          (bunchedBimonoidAugAndJoin cleanA
                            (bunchedBimonoidAugAndJoin cleanB composeABC))
                          (bunchedBimonoidAugAndJoin cleanC composeBC)
      · match bunchedBimonoidAugAndSplit cleanLeft with
        | ⟨cleanAB, _⟩ =>
            match bunchedBimonoidAugAndSplit cleanAB with
            | ⟨_, restAB⟩ =>
                match bunchedBimonoidAugAndSplit restAB with
                | ⟨_, composeAB⟩ =>
                    exact (bunchedBimonoidMatMulAssoc (bunchedBimonoidEvalAugCell cellC)
                      (bunchedBimonoidEvalAugCell cellB) (bunchedBimonoidEvalAugCell cellA)
                      (bunchedBimonoidNatEqOfBeqTrue _ _ composeAB).symm).symm
  | _ + 2 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩

/-- vcompUnitLeft is absorbed. -/
theorem bunchedBimonoidAugGatedVcompUnitLeft {dim : Nat}
    (cellA : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidAugGatedEq
      (CellExpr.vcomp (CellExpr.id (boundarySource cellA)) cellA) cellA := by
  match dim with
  | 0 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ =>
      Nat.zero_add (bunchedBimonoidEvalAugCell cellA)⟩
  | 1 =>
      refine ⟨Iff.intro (fun cleanLeft => (bunchedBimonoidAugAndSplit
          (bunchedBimonoidAugAndSplit cleanLeft).2).1) (fun cleanA => ?_), fun _ cleanA => ?_⟩
      · refine bunchedBimonoidAugAndJoin
          (bunchedBimonoidAugCleanOneCell (boundarySource cellA))
          (bunchedBimonoidAugAndJoin cleanA
            (bunchedBimonoidDecideEqTrue (bunchedBimonoidAugColsEq cellA).symm))
      · show bunchedBimonoidMatMul (bunchedBimonoidEvalAugCell cellA)
          (bunchedBimonoidIdentityMat
            (Nat.add (bunchedBimonoidAugWordWidth (boundarySource cellA)) 1))
          = bunchedBimonoidEvalAugCell cellA
        rw [show Nat.add (bunchedBimonoidAugWordWidth (boundarySource cellA)) 1
          = (bunchedBimonoidEvalAugCell cellA).cols from (bunchedBimonoidAugColsEq cellA).symm]
        exact bunchedBimonoidIdentityRightUnit (bunchedBimonoidEvalAugCell cellA)
          (bunchedBimonoidAugWellFormedEval cellA)
  | _ + 2 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩

/-- vcompUnitRight is absorbed. -/
theorem bunchedBimonoidAugGatedVcompUnitRight {dim : Nat}
    (cellA : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidAugGatedEq
      (CellExpr.vcomp cellA (CellExpr.id (boundaryTarget cellA))) cellA := by
  match dim with
  | 0 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩
  | 1 =>
      refine ⟨Iff.intro (fun cleanLeft => (bunchedBimonoidAugAndSplit cleanLeft).1)
        (fun cleanA => ?_), fun _ cleanA => ?_⟩
      · refine bunchedBimonoidAugAndJoin cleanA
          (bunchedBimonoidAugAndJoin
            (bunchedBimonoidAugCleanOneCell (boundaryTarget cellA))
            (bunchedBimonoidDecideEqTrue (bunchedBimonoidAugRowsEq cellA)))
      · show bunchedBimonoidMatMul
          (bunchedBimonoidIdentityMat
            (Nat.add (bunchedBimonoidAugWordWidth (boundaryTarget cellA)) 1))
          (bunchedBimonoidEvalAugCell cellA)
          = bunchedBimonoidEvalAugCell cellA
        rw [show Nat.add (bunchedBimonoidAugWordWidth (boundaryTarget cellA)) 1
          = (bunchedBimonoidEvalAugCell cellA).rows from (bunchedBimonoidAugRowsEq cellA).symm]
        exact bunchedBimonoidIdentityLeftUnit (bunchedBimonoidEvalAugCell cellA)
          (bunchedBimonoidAugWellFormedEval cellA)
  | _ + 2 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩

/-- whiskerLeftUnit is absorbed. -/
theorem bunchedBimonoidAugGatedWhiskerLeftUnit {dim : Nat}
    (whiskeringCell innerCell : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidAugGatedEq
      (CellExpr.whiskerLeft whiskeringCell (CellExpr.id innerCell))
      (CellExpr.id (CellExpr.vcomp whiskeringCell innerCell)) := by
  match dim with
  | 0 =>
      refine ⟨Iff.intro
        (fun _ => bunchedBimonoidAugCleanOneCell (CellExpr.vcomp whiskeringCell innerCell))
        (fun _ => bunchedBimonoidAugAndJoin
          (bunchedBimonoidAugCleanOneCell whiskeringCell)
          (bunchedBimonoidAugCleanOneCell innerCell)), fun _ _ => ?_⟩
      show bunchedBimonoidAugPointedLeft (bunchedBimonoidAugWordWidth whiskeringCell)
          (bunchedBimonoidIdentityMat (Nat.add (bunchedBimonoidAugWordWidth innerCell) 1))
        = bunchedBimonoidIdentityMat
            (Nat.add (Nat.add (bunchedBimonoidAugWordWidth whiskeringCell)
              (bunchedBimonoidAugWordWidth innerCell)) 1)
      rw [bunchedBimonoidAugPointedLeftAsTensor (bunchedBimonoidAugWordWidth whiskeringCell)
        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth innerCell + 1))
        (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)]
      rw [bunchedBimonoidAugPointedTensorIdentity (bunchedBimonoidAugWordWidth whiskeringCell)
        (bunchedBimonoidAugWordWidth innerCell)]
      exact congrArg bunchedBimonoidIdentityMat
        (bunchedBimonoidAugSuccAddShuffle (bunchedBimonoidAugWordWidth whiskeringCell)
          (bunchedBimonoidAugWordWidth innerCell))
  | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩

/-- whiskerRightUnit is absorbed. -/
theorem bunchedBimonoidAugGatedWhiskerRightUnit {dim : Nat}
    (innerCell whiskeringCell : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidAugGatedEq
      (CellExpr.whiskerRight (CellExpr.id innerCell) whiskeringCell)
      (CellExpr.id (CellExpr.vcomp innerCell whiskeringCell)) := by
  match dim with
  | 0 =>
      refine ⟨Iff.intro
        (fun _ => bunchedBimonoidAugCleanOneCell (CellExpr.vcomp innerCell whiskeringCell))
        (fun _ => bunchedBimonoidAugAndJoin
          (bunchedBimonoidAugCleanOneCell innerCell)
          (bunchedBimonoidAugCleanOneCell whiskeringCell)), fun _ _ => ?_⟩
      show bunchedBimonoidAugPointedRight
          (bunchedBimonoidIdentityMat (Nat.add (bunchedBimonoidAugWordWidth innerCell) 1))
          (bunchedBimonoidAugWordWidth whiskeringCell)
        = bunchedBimonoidIdentityMat
            (Nat.add (Nat.add (bunchedBimonoidAugWordWidth innerCell)
              (bunchedBimonoidAugWordWidth whiskeringCell)) 1)
      rw [bunchedBimonoidAugPointedRightAsTensor
        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth innerCell + 1))
        (bunchedBimonoidAugWordWidth whiskeringCell) (Nat.zero_lt_succ _)]
      rw [bunchedBimonoidAugPointedTensorIdentity (bunchedBimonoidAugWordWidth innerCell)
        (bunchedBimonoidAugWordWidth whiskeringCell)]
      exact congrArg bunchedBimonoidIdentityMat
        (Nat.succ_add (bunchedBimonoidAugWordWidth innerCell)
          (bunchedBimonoidAugWordWidth whiskeringCell))
  | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩

/-- whiskerLeftFunctorial is absorbed. -/
theorem bunchedBimonoidAugGatedWhiskerLeftFunctorial {dim : Nat}
    (whiskeringCell : CellExpr bunchedBimonoidOmegaComputad (dim + 1))
    (cellBeta cellGamma : CellExpr bunchedBimonoidOmegaComputad (dim + 2)) :
    bunchedBimonoidAugGatedEq
      (CellExpr.whiskerLeft whiskeringCell (CellExpr.vcomp cellBeta cellGamma))
      (CellExpr.vcomp (CellExpr.whiskerLeft whiskeringCell cellBeta)
        (CellExpr.whiskerLeft whiskeringCell cellGamma)) := by
  match dim with
  | 0 =>
      refine ⟨Iff.intro (fun cleanLeft => ?_) (fun cleanRight => ?_), fun cleanLeft _ => ?_⟩
      · match bunchedBimonoidAugAndSplit cleanLeft with
        | ⟨cleanW, cleanBC⟩ =>
            match bunchedBimonoidAugAndSplit cleanBC with
            | ⟨cleanB, restBC⟩ =>
                match bunchedBimonoidAugAndSplit restBC with
                | ⟨cleanC, composeBC⟩ =>
                    refine bunchedBimonoidAugAndJoin
                      (bunchedBimonoidAugAndJoin cleanW cleanB)
                      (bunchedBimonoidAugAndJoin
                        (bunchedBimonoidAugAndJoin cleanW cleanC) ?_)
                    show ((bunchedBimonoidAugWordWidth whiskeringCell
                        + (bunchedBimonoidEvalAugCell cellBeta).rows)
                      == (bunchedBimonoidAugWordWidth whiskeringCell
                        + (bunchedBimonoidEvalAugCell cellGamma).cols)) = true
                    rw [bunchedBimonoidAugBeqShiftCancelLeft]
                    exact composeBC
      · match bunchedBimonoidAugAndSplit cleanRight with
        | ⟨cleanWB, restRight⟩ =>
            match bunchedBimonoidAugAndSplit restRight with
            | ⟨cleanWC, composeWBC⟩ =>
                match bunchedBimonoidAugAndSplit cleanWB, bunchedBimonoidAugAndSplit cleanWC with
                | ⟨cleanW, cleanB⟩, ⟨_, cleanC⟩ =>
                    refine bunchedBimonoidAugAndJoin cleanW
                      (bunchedBimonoidAugAndJoin cleanB
                        (bunchedBimonoidAugAndJoin cleanC ?_))
                    have shifted : ((bunchedBimonoidAugWordWidth whiskeringCell
                        + (bunchedBimonoidEvalAugCell cellBeta).rows)
                      == (bunchedBimonoidAugWordWidth whiskeringCell
                        + (bunchedBimonoidEvalAugCell cellGamma).cols)) = true := composeWBC
                    rw [bunchedBimonoidAugBeqShiftCancelLeft] at shifted
                    exact shifted
      · match bunchedBimonoidAugAndSplit cleanLeft with
        | ⟨_, cleanBC⟩ =>
            match bunchedBimonoidAugAndSplit cleanBC with
            | ⟨_, restBC⟩ =>
                match bunchedBimonoidAugAndSplit restBC with
                | ⟨_, composeBC⟩ =>
                    show bunchedBimonoidAugPointedLeft (bunchedBimonoidAugWordWidth whiskeringCell)
                        (bunchedBimonoidMatMul (bunchedBimonoidEvalAugCell cellGamma)
                          (bunchedBimonoidEvalAugCell cellBeta))
                      = bunchedBimonoidMatMul
                          (bunchedBimonoidAugPointedLeft
                            (bunchedBimonoidAugWordWidth whiskeringCell)
                            (bunchedBimonoidEvalAugCell cellGamma))
                          (bunchedBimonoidAugPointedLeft
                            (bunchedBimonoidAugWordWidth whiskeringCell)
                            (bunchedBimonoidEvalAugCell cellBeta))
                    rw [bunchedBimonoidAugPointedLeftAsTensor
                      (bunchedBimonoidAugWordWidth whiskeringCell)
                      (bunchedBimonoidMatMul (bunchedBimonoidEvalAugCell cellGamma)
                        (bunchedBimonoidEvalAugCell cellBeta))
                      (bunchedBimonoidAugRowsPos cellGamma) (bunchedBimonoidAugColsPos cellBeta)]
                    rw [bunchedBimonoidAugPointedLeftAsTensor
                      (bunchedBimonoidAugWordWidth whiskeringCell)
                      (bunchedBimonoidEvalAugCell cellGamma)
                      (bunchedBimonoidAugRowsPos cellGamma) (bunchedBimonoidAugColsPos cellGamma)]
                    rw [bunchedBimonoidAugPointedLeftAsTensor
                      (bunchedBimonoidAugWordWidth whiskeringCell)
                      (bunchedBimonoidEvalAugCell cellBeta)
                      (bunchedBimonoidAugRowsPos cellBeta) (bunchedBimonoidAugColsPos cellBeta)]
                    rw [bunchedBimonoidAugPointedTensorMul
                      (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1))
                      (bunchedBimonoidEvalAugCell cellGamma)
                      (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1))
                      (bunchedBimonoidEvalAugCell cellBeta)
                      rfl
                      (bunchedBimonoidAugIdentityHeaded (bunchedBimonoidAugWordWidth whiskeringCell))
                      (bunchedBimonoidAugHeadedEval cellBeta)
                      (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
                      (bunchedBimonoidAugRowsPos cellBeta) (bunchedBimonoidAugColsPos cellBeta)
                      (bunchedBimonoidAugColsPos cellGamma)
                      (bunchedBimonoidAugWellFormedEval cellGamma)]
                    rw [show bunchedBimonoidMatMul
                        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1))
                        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1))
                      = bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1)
                      from bunchedBimonoidIdentityRightUnit
                        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1))
                        (bunchedBimonoidAugIdentityMatWellFormed _)]
  | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩

/-- whiskerRightFunctorial is absorbed. -/
theorem bunchedBimonoidAugGatedWhiskerRightFunctorial {dim : Nat}
    (cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad (dim + 2))
    (whiskeringCell : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidAugGatedEq
      (CellExpr.whiskerRight (CellExpr.vcomp cellAlpha cellBeta) whiskeringCell)
      (CellExpr.vcomp (CellExpr.whiskerRight cellAlpha whiskeringCell)
        (CellExpr.whiskerRight cellBeta whiskeringCell)) := by
  match dim with
  | 0 =>
      refine ⟨Iff.intro (fun cleanLeft => ?_) (fun cleanRight => ?_), fun cleanLeft _ => ?_⟩
      · match bunchedBimonoidAugAndSplit cleanLeft with
        | ⟨cleanAB, cleanW⟩ =>
            match bunchedBimonoidAugAndSplit cleanAB with
            | ⟨cleanA, restAB⟩ =>
                match bunchedBimonoidAugAndSplit restAB with
                | ⟨cleanB, composeAB⟩ =>
                    refine bunchedBimonoidAugAndJoin
                      (bunchedBimonoidAugAndJoin cleanA cleanW)
                      (bunchedBimonoidAugAndJoin
                        (bunchedBimonoidAugAndJoin cleanB cleanW) ?_)
                    show (((bunchedBimonoidEvalAugCell cellAlpha).rows
                        + bunchedBimonoidAugWordWidth whiskeringCell)
                      == ((bunchedBimonoidEvalAugCell cellBeta).cols
                        + bunchedBimonoidAugWordWidth whiskeringCell)) = true
                    rw [bunchedBimonoidAugBeqShiftCancelRight]
                    exact composeAB
      · match bunchedBimonoidAugAndSplit cleanRight with
        | ⟨cleanAW, restRight⟩ =>
            match bunchedBimonoidAugAndSplit restRight with
            | ⟨cleanBW, composeAWB⟩ =>
                match bunchedBimonoidAugAndSplit cleanAW, bunchedBimonoidAugAndSplit cleanBW with
                | ⟨cleanA, cleanW⟩, ⟨cleanB, _⟩ =>
                    refine bunchedBimonoidAugAndJoin
                      (bunchedBimonoidAugAndJoin cleanA
                        (bunchedBimonoidAugAndJoin cleanB ?_)) cleanW
                    have shifted : (((bunchedBimonoidEvalAugCell cellAlpha).rows
                        + bunchedBimonoidAugWordWidth whiskeringCell)
                      == ((bunchedBimonoidEvalAugCell cellBeta).cols
                        + bunchedBimonoidAugWordWidth whiskeringCell)) = true := composeAWB
                    rw [bunchedBimonoidAugBeqShiftCancelRight] at shifted
                    exact shifted
      · match bunchedBimonoidAugAndSplit cleanLeft with
        | ⟨cleanAB, _⟩ =>
            match bunchedBimonoidAugAndSplit cleanAB with
            | ⟨_, restAB⟩ =>
                match bunchedBimonoidAugAndSplit restAB with
                | ⟨_, composeAB⟩ =>
                    show bunchedBimonoidAugPointedRight
                        (bunchedBimonoidMatMul (bunchedBimonoidEvalAugCell cellBeta)
                          (bunchedBimonoidEvalAugCell cellAlpha))
                        (bunchedBimonoidAugWordWidth whiskeringCell)
                      = bunchedBimonoidMatMul
                          (bunchedBimonoidAugPointedRight (bunchedBimonoidEvalAugCell cellBeta)
                            (bunchedBimonoidAugWordWidth whiskeringCell))
                          (bunchedBimonoidAugPointedRight (bunchedBimonoidEvalAugCell cellAlpha)
                            (bunchedBimonoidAugWordWidth whiskeringCell))
                    rw [bunchedBimonoidAugPointedRightAsTensor
                      (bunchedBimonoidMatMul (bunchedBimonoidEvalAugCell cellBeta)
                        (bunchedBimonoidEvalAugCell cellAlpha))
                      (bunchedBimonoidAugWordWidth whiskeringCell)
                      (bunchedBimonoidAugColsPos cellAlpha)]
                    rw [bunchedBimonoidAugPointedRightAsTensor (bunchedBimonoidEvalAugCell cellBeta)
                      (bunchedBimonoidAugWordWidth whiskeringCell)
                      (bunchedBimonoidAugColsPos cellBeta)]
                    rw [bunchedBimonoidAugPointedRightAsTensor (bunchedBimonoidEvalAugCell cellAlpha)
                      (bunchedBimonoidAugWordWidth whiskeringCell)
                      (bunchedBimonoidAugColsPos cellAlpha)]
                    rw [bunchedBimonoidAugPointedTensorMul (bunchedBimonoidEvalAugCell cellBeta)
                      (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1))
                      (bunchedBimonoidEvalAugCell cellAlpha)
                      (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1))
                      (bunchedBimonoidNatEqOfBeqTrue _ _ composeAB).symm
                      (bunchedBimonoidAugHeadedEval cellAlpha)
                      (bunchedBimonoidAugIdentityHeaded (bunchedBimonoidAugWordWidth whiskeringCell))
                      (bunchedBimonoidAugRowsPos cellAlpha) (bunchedBimonoidAugColsPos cellAlpha)
                      (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
                      (Nat.zero_lt_succ _)
                      (bunchedBimonoidAugIdentityMatWellFormed _)]
                    rw [show bunchedBimonoidMatMul
                        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1))
                        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1))
                      = bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1)
                      from bunchedBimonoidIdentityRightUnit
                        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskeringCell + 1))
                        (bunchedBimonoidAugIdentityMatWellFormed _)]
  | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩

/-- The Godement interchange is absorbed. -/
theorem bunchedBimonoidAugGatedInterchange {dim : Nat}
    (cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad (dim + 2)) :
    bunchedBimonoidAugGatedEq
      (CellExpr.vcomp (CellExpr.whiskerRight cellAlpha (boundarySource cellBeta))
        (CellExpr.whiskerLeft (boundaryTarget cellAlpha) cellBeta))
      (CellExpr.vcomp (CellExpr.whiskerLeft (boundarySource cellAlpha) cellBeta)
        (CellExpr.whiskerRight cellAlpha (boundaryTarget cellBeta))) := by
  match dim with
  | 0 =>
      have leftComposable : (((bunchedBimonoidEvalAugCell cellAlpha).rows
            + bunchedBimonoidAugWordWidth (boundarySource cellBeta))
          == (bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha)
            + (bunchedBimonoidEvalAugCell cellBeta).cols)) = true := by
        refine bunchedBimonoidDecideEqTrue ?_
        rw [bunchedBimonoidAugRowsEq cellAlpha, bunchedBimonoidAugColsEq cellBeta]
        exact bunchedBimonoidAugSuccAddShuffle
          (bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha))
          (bunchedBimonoidAugWordWidth (boundarySource cellBeta))
      have rightComposable : ((bunchedBimonoidAugWordWidth (boundarySource cellAlpha)
            + (bunchedBimonoidEvalAugCell cellBeta).rows)
          == ((bunchedBimonoidEvalAugCell cellAlpha).cols
            + bunchedBimonoidAugWordWidth (boundaryTarget cellBeta))) = true := by
        refine bunchedBimonoidDecideEqTrue ?_
        rw [bunchedBimonoidAugRowsEq cellBeta, bunchedBimonoidAugColsEq cellAlpha]
        exact (bunchedBimonoidAugSuccAddShuffle
          (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))
          (bunchedBimonoidAugWordWidth (boundaryTarget cellBeta))).symm
      refine ⟨Iff.intro (fun cleanLeft => ?_) (fun cleanRight => ?_), fun cleanLeft _ => ?_⟩
      · match bunchedBimonoidAugAndSplit cleanLeft with
        | ⟨cleanAW, restLeft⟩ =>
            match bunchedBimonoidAugAndSplit restLeft with
            | ⟨cleanWB, _⟩ =>
                match bunchedBimonoidAugAndSplit cleanAW, bunchedBimonoidAugAndSplit cleanWB with
                | ⟨cleanA, _⟩, ⟨_, cleanB⟩ =>
                    exact bunchedBimonoidAugAndJoin
                      (bunchedBimonoidAugAndJoin
                        (bunchedBimonoidAugCleanOneCell (boundarySource cellAlpha)) cleanB)
                      (bunchedBimonoidAugAndJoin
                        (bunchedBimonoidAugAndJoin cleanA
                          (bunchedBimonoidAugCleanOneCell (boundaryTarget cellBeta)))
                        rightComposable)
      · match bunchedBimonoidAugAndSplit cleanRight with
        | ⟨cleanWB, restRight⟩ =>
            match bunchedBimonoidAugAndSplit restRight with
            | ⟨cleanAW, _⟩ =>
                match bunchedBimonoidAugAndSplit cleanWB, bunchedBimonoidAugAndSplit cleanAW with
                | ⟨_, cleanB⟩, ⟨cleanA, _⟩ =>
                    exact bunchedBimonoidAugAndJoin
                      (bunchedBimonoidAugAndJoin cleanA
                        (bunchedBimonoidAugCleanOneCell (boundarySource cellBeta)))
                      (bunchedBimonoidAugAndJoin
                        (bunchedBimonoidAugAndJoin
                          (bunchedBimonoidAugCleanOneCell (boundaryTarget cellAlpha)) cleanB)
                        leftComposable)
      · show bunchedBimonoidMatMul
            (bunchedBimonoidAugPointedLeft
              (bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha))
              (bunchedBimonoidEvalAugCell cellBeta))
            (bunchedBimonoidAugPointedRight (bunchedBimonoidEvalAugCell cellAlpha)
              (bunchedBimonoidAugWordWidth (boundarySource cellBeta)))
          = bunchedBimonoidMatMul
              (bunchedBimonoidAugPointedRight (bunchedBimonoidEvalAugCell cellAlpha)
                (bunchedBimonoidAugWordWidth (boundaryTarget cellBeta)))
              (bunchedBimonoidAugPointedLeft
                (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))
                (bunchedBimonoidEvalAugCell cellBeta))
        rw [bunchedBimonoidAugPointedLeftAsTensor
          (bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha))
          (bunchedBimonoidEvalAugCell cellBeta)
          (bunchedBimonoidAugRowsPos cellBeta) (bunchedBimonoidAugColsPos cellBeta)]
        rw [bunchedBimonoidAugPointedLeftAsTensor
          (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))
          (bunchedBimonoidEvalAugCell cellBeta)
          (bunchedBimonoidAugRowsPos cellBeta) (bunchedBimonoidAugColsPos cellBeta)]
        rw [bunchedBimonoidAugPointedRightAsTensor (bunchedBimonoidEvalAugCell cellAlpha)
          (bunchedBimonoidAugWordWidth (boundarySource cellBeta))
          (bunchedBimonoidAugColsPos cellAlpha)]
        rw [bunchedBimonoidAugPointedRightAsTensor (bunchedBimonoidEvalAugCell cellAlpha)
          (bunchedBimonoidAugWordWidth (boundaryTarget cellBeta))
          (bunchedBimonoidAugColsPos cellAlpha)]
        rw [bunchedBimonoidAugPointedTensorMul
          (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha) + 1))
          (bunchedBimonoidEvalAugCell cellBeta)
          (bunchedBimonoidEvalAugCell cellAlpha)
          (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth (boundarySource cellBeta) + 1))
          (show (bunchedBimonoidIdentityMat
              (bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha) + 1)).cols
            = (bunchedBimonoidEvalAugCell cellAlpha).rows from
            (bunchedBimonoidAugRowsEq cellAlpha).symm)
          (bunchedBimonoidAugHeadedEval cellAlpha)
          (bunchedBimonoidAugIdentityHeaded
            (bunchedBimonoidAugWordWidth (boundarySource cellBeta)))
          (bunchedBimonoidAugRowsPos cellAlpha) (bunchedBimonoidAugColsPos cellAlpha)
          (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          (bunchedBimonoidAugColsPos cellBeta)
          (bunchedBimonoidAugWellFormedEval cellBeta)]
        rw [bunchedBimonoidAugPointedTensorMul (bunchedBimonoidEvalAugCell cellAlpha)
          (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth (boundaryTarget cellBeta) + 1))
          (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth (boundarySource cellAlpha) + 1))
          (bunchedBimonoidEvalAugCell cellBeta)
          (show (bunchedBimonoidEvalAugCell cellAlpha).cols
            = (bunchedBimonoidIdentityMat
              (bunchedBimonoidAugWordWidth (boundarySource cellAlpha) + 1)).rows from
            bunchedBimonoidAugColsEq cellAlpha)
          (bunchedBimonoidAugIdentityHeaded
            (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))
          (bunchedBimonoidAugHeadedEval cellBeta)
          (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          (bunchedBimonoidAugRowsPos cellBeta) (bunchedBimonoidAugColsPos cellBeta)
          (Nat.zero_lt_succ _)
          (bunchedBimonoidAugIdentityMatWellFormed _)]
        rw [show bunchedBimonoidMatMul
            (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha) + 1))
            (bunchedBimonoidEvalAugCell cellAlpha)
          = bunchedBimonoidEvalAugCell cellAlpha from by
          rw [show bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha) + 1
            = (bunchedBimonoidEvalAugCell cellAlpha).rows from
            (bunchedBimonoidAugRowsEq cellAlpha).symm]
          exact bunchedBimonoidIdentityLeftUnit (bunchedBimonoidEvalAugCell cellAlpha)
            (bunchedBimonoidAugWellFormedEval cellAlpha)]
        rw [show bunchedBimonoidMatMul (bunchedBimonoidEvalAugCell cellBeta)
            (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth (boundarySource cellBeta) + 1))
          = bunchedBimonoidEvalAugCell cellBeta from by
          rw [show bunchedBimonoidAugWordWidth (boundarySource cellBeta) + 1
            = (bunchedBimonoidEvalAugCell cellBeta).cols from
            (bunchedBimonoidAugColsEq cellBeta).symm]
          exact bunchedBimonoidIdentityRightUnit (bunchedBimonoidEvalAugCell cellBeta)
            (bunchedBimonoidAugWellFormedEval cellBeta)]
        rw [show bunchedBimonoidMatMul (bunchedBimonoidEvalAugCell cellAlpha)
            (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth (boundarySource cellAlpha) + 1))
          = bunchedBimonoidEvalAugCell cellAlpha from by
          rw [show bunchedBimonoidAugWordWidth (boundarySource cellAlpha) + 1
            = (bunchedBimonoidEvalAugCell cellAlpha).cols from
            (bunchedBimonoidAugColsEq cellAlpha).symm]
          exact bunchedBimonoidIdentityRightUnit (bunchedBimonoidEvalAugCell cellAlpha)
            (bunchedBimonoidAugWellFormedEval cellAlpha)]
        rw [show bunchedBimonoidMatMul
            (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth (boundaryTarget cellBeta) + 1))
            (bunchedBimonoidEvalAugCell cellBeta)
          = bunchedBimonoidEvalAugCell cellBeta from by
          rw [show bunchedBimonoidAugWordWidth (boundaryTarget cellBeta) + 1
            = (bunchedBimonoidEvalAugCell cellBeta).rows from
            (bunchedBimonoidAugRowsEq cellBeta).symm]
          exact bunchedBimonoidIdentityLeftUnit (bunchedBimonoidEvalAugCell cellBeta)
            (bunchedBimonoidAugWellFormedEval cellBeta)]
  | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩

/-- whiskerAssocLeft is absorbed. -/
theorem bunchedBimonoidAugGatedWhiskerAssocLeft {dim : Nat}
    (whiskP whiskQ : CellExpr bunchedBimonoidOmegaComputad (dim + 1))
    (innerCell : CellExpr bunchedBimonoidOmegaComputad (dim + 2)) :
    bunchedBimonoidAugGatedEq
      (CellExpr.whiskerLeft (CellExpr.vcomp whiskP whiskQ) innerCell)
      (CellExpr.whiskerLeft whiskP (CellExpr.whiskerLeft whiskQ innerCell)) := by
  match dim with
  | 0 =>
      refine ⟨Iff.intro
        (fun cleanLeft => bunchedBimonoidAugAndJoin (bunchedBimonoidAugCleanOneCell whiskP)
          (bunchedBimonoidAugAndJoin (bunchedBimonoidAugCleanOneCell whiskQ)
            (bunchedBimonoidAugAndSplit cleanLeft).2))
        (fun cleanRight => bunchedBimonoidAugAndJoin
          (bunchedBimonoidAugCleanOneCell (CellExpr.vcomp whiskP whiskQ))
          (bunchedBimonoidAugAndSplit (bunchedBimonoidAugAndSplit cleanRight).2).2),
        fun _ _ => ?_⟩
      show bunchedBimonoidAugPointedLeft
          (Nat.add (bunchedBimonoidAugWordWidth whiskP) (bunchedBimonoidAugWordWidth whiskQ))
          (bunchedBimonoidEvalAugCell innerCell)
        = bunchedBimonoidAugPointedLeft (bunchedBimonoidAugWordWidth whiskP)
            (bunchedBimonoidAugPointedLeft (bunchedBimonoidAugWordWidth whiskQ)
              (bunchedBimonoidEvalAugCell innerCell))
      rw [bunchedBimonoidAugPointedLeftAsTensor
        (Nat.add (bunchedBimonoidAugWordWidth whiskP) (bunchedBimonoidAugWordWidth whiskQ))
        (bunchedBimonoidEvalAugCell innerCell)
        (bunchedBimonoidAugRowsPos innerCell) (bunchedBimonoidAugColsPos innerCell)]
      rw [bunchedBimonoidAugPointedLeftAsTensor (bunchedBimonoidAugWordWidth whiskQ)
        (bunchedBimonoidEvalAugCell innerCell)
        (bunchedBimonoidAugRowsPos innerCell) (bunchedBimonoidAugColsPos innerCell)]
      rw [bunchedBimonoidAugPointedLeftAsTensor (bunchedBimonoidAugWordWidth whiskP)
        (bunchedBimonoidAugPointedTensor
          (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskQ + 1))
          (bunchedBimonoidEvalAugCell innerCell))
        (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_add_right _ _))
        (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_add_right _ _))]
      rw [bunchedBimonoidAugPointedTensorAssoc
        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskP + 1))
        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskQ + 1))
        (bunchedBimonoidEvalAugCell innerCell)
        (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)]
      rw [bunchedBimonoidAugPointedTensorIdentity (bunchedBimonoidAugWordWidth whiskP)
        (bunchedBimonoidAugWordWidth whiskQ)]
      exact congrArg (fun dimension => bunchedBimonoidAugPointedTensor
        (bunchedBimonoidIdentityMat dimension) (bunchedBimonoidEvalAugCell innerCell))
        (bunchedBimonoidAugSuccAddShuffle (bunchedBimonoidAugWordWidth whiskP)
          (bunchedBimonoidAugWordWidth whiskQ)).symm
  | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩

/-- whiskerAssocRight is absorbed. -/
theorem bunchedBimonoidAugGatedWhiskerAssocRight {dim : Nat}
    (innerCell : CellExpr bunchedBimonoidOmegaComputad (dim + 2))
    (whiskP whiskQ : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidAugGatedEq
      (CellExpr.whiskerRight innerCell (CellExpr.vcomp whiskP whiskQ))
      (CellExpr.whiskerRight (CellExpr.whiskerRight innerCell whiskP) whiskQ) := by
  match dim with
  | 0 =>
      refine ⟨Iff.intro
        (fun cleanLeft => bunchedBimonoidAugAndJoin
          (bunchedBimonoidAugAndJoin (bunchedBimonoidAugAndSplit cleanLeft).1
            (bunchedBimonoidAugCleanOneCell whiskP))
          (bunchedBimonoidAugCleanOneCell whiskQ))
        (fun cleanRight => bunchedBimonoidAugAndJoin
          (bunchedBimonoidAugAndSplit (bunchedBimonoidAugAndSplit cleanRight).1).1
          (bunchedBimonoidAugCleanOneCell (CellExpr.vcomp whiskP whiskQ))),
        fun _ _ => ?_⟩
      show bunchedBimonoidAugPointedRight (bunchedBimonoidEvalAugCell innerCell)
          (Nat.add (bunchedBimonoidAugWordWidth whiskP) (bunchedBimonoidAugWordWidth whiskQ))
        = bunchedBimonoidAugPointedRight
            (bunchedBimonoidAugPointedRight (bunchedBimonoidEvalAugCell innerCell)
              (bunchedBimonoidAugWordWidth whiskP))
            (bunchedBimonoidAugWordWidth whiskQ)
      rw [bunchedBimonoidAugPointedRightAsTensor (bunchedBimonoidEvalAugCell innerCell)
        (Nat.add (bunchedBimonoidAugWordWidth whiskP) (bunchedBimonoidAugWordWidth whiskQ))
        (bunchedBimonoidAugColsPos innerCell)]
      rw [bunchedBimonoidAugPointedRightAsTensor (bunchedBimonoidEvalAugCell innerCell)
        (bunchedBimonoidAugWordWidth whiskP) (bunchedBimonoidAugColsPos innerCell)]
      rw [bunchedBimonoidAugPointedRightAsTensor
        (bunchedBimonoidAugPointedTensor (bunchedBimonoidEvalAugCell innerCell)
          (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskP + 1)))
        (bunchedBimonoidAugWordWidth whiskQ)
        (Nat.lt_of_lt_of_le (bunchedBimonoidAugColsPos innerCell) (Nat.le_add_right _ _))]
      rw [← bunchedBimonoidAugPointedTensorAssoc (bunchedBimonoidEvalAugCell innerCell)
        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskP + 1))
        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskQ + 1))
        (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (bunchedBimonoidAugColsPos innerCell)]
      rw [bunchedBimonoidAugPointedTensorIdentity (bunchedBimonoidAugWordWidth whiskP)
        (bunchedBimonoidAugWordWidth whiskQ)]
      exact congrArg (fun dimension => bunchedBimonoidAugPointedTensor
        (bunchedBimonoidEvalAugCell innerCell) (bunchedBimonoidIdentityMat dimension))
        (bunchedBimonoidAugSuccAddShuffle (bunchedBimonoidAugWordWidth whiskP)
          (bunchedBimonoidAugWordWidth whiskQ)).symm
  | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩

/-- whiskerLeftRightCommute is absorbed. -/
theorem bunchedBimonoidAugGatedWhiskerLeftRightCommute {dim : Nat}
    (whiskP : CellExpr bunchedBimonoidOmegaComputad (dim + 1))
    (innerCell : CellExpr bunchedBimonoidOmegaComputad (dim + 2))
    (whiskQ : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidAugGatedEq
      (CellExpr.whiskerRight (CellExpr.whiskerLeft whiskP innerCell) whiskQ)
      (CellExpr.whiskerLeft whiskP (CellExpr.whiskerRight innerCell whiskQ)) := by
  match dim with
  | 0 =>
      refine ⟨Iff.intro
        (fun cleanLeft => bunchedBimonoidAugAndJoin (bunchedBimonoidAugCleanOneCell whiskP)
          (bunchedBimonoidAugAndJoin
            (bunchedBimonoidAugAndSplit (bunchedBimonoidAugAndSplit cleanLeft).1).2
            (bunchedBimonoidAugCleanOneCell whiskQ)))
        (fun cleanRight => bunchedBimonoidAugAndJoin
          (bunchedBimonoidAugAndJoin (bunchedBimonoidAugCleanOneCell whiskP)
            (bunchedBimonoidAugAndSplit (bunchedBimonoidAugAndSplit cleanRight).2).1)
          (bunchedBimonoidAugCleanOneCell whiskQ)),
        fun _ _ => ?_⟩
      show bunchedBimonoidAugPointedRight
          (bunchedBimonoidAugPointedLeft (bunchedBimonoidAugWordWidth whiskP)
            (bunchedBimonoidEvalAugCell innerCell))
          (bunchedBimonoidAugWordWidth whiskQ)
        = bunchedBimonoidAugPointedLeft (bunchedBimonoidAugWordWidth whiskP)
            (bunchedBimonoidAugPointedRight (bunchedBimonoidEvalAugCell innerCell)
              (bunchedBimonoidAugWordWidth whiskQ))
      rw [bunchedBimonoidAugPointedLeftAsTensor (bunchedBimonoidAugWordWidth whiskP)
        (bunchedBimonoidEvalAugCell innerCell)
        (bunchedBimonoidAugRowsPos innerCell) (bunchedBimonoidAugColsPos innerCell)]
      rw [bunchedBimonoidAugPointedRightAsTensor
        (bunchedBimonoidAugPointedTensor
          (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskP + 1))
          (bunchedBimonoidEvalAugCell innerCell))
        (bunchedBimonoidAugWordWidth whiskQ)
        (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_add_right _ _))]
      rw [bunchedBimonoidAugPointedRightAsTensor (bunchedBimonoidEvalAugCell innerCell)
        (bunchedBimonoidAugWordWidth whiskQ) (bunchedBimonoidAugColsPos innerCell)]
      rw [bunchedBimonoidAugPointedLeftAsTensor (bunchedBimonoidAugWordWidth whiskP)
        (bunchedBimonoidAugPointedTensor (bunchedBimonoidEvalAugCell innerCell)
          (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskQ + 1)))
        (Nat.lt_of_lt_of_le (bunchedBimonoidAugRowsPos innerCell) (Nat.le_add_right _ _))
        (Nat.lt_of_lt_of_le (bunchedBimonoidAugColsPos innerCell) (Nat.le_add_right _ _))]
      exact (bunchedBimonoidAugPointedTensorAssoc
        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskP + 1))
        (bunchedBimonoidEvalAugCell innerCell)
        (bunchedBimonoidIdentityMat (bunchedBimonoidAugWordWidth whiskQ + 1))
        (bunchedBimonoidAugRowsPos innerCell) (bunchedBimonoidAugColsPos innerCell)
        (Nat.zero_lt_succ _)).symm
  | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩

/-! # =========================================================================================
    # E2 — THE ABSORBER INSTANCE + THE FOLD
    # =========================================================================================
-/

/-- ★★★ **THE GATED AFFINE ABSORBER** — the gated augmented-equality relation absorbs the idCongr-extended
saturated congruence over the FULL star scope (`StrictAxiomRel union SoundRow union HexagonRow`): every strict
row via the pointed-tensor algebra (Clean instances) and Clean-equivalence (junk instances vacuous); every
sound/hexagon row by direct computation; every congruence field by Clean-transport + `congrArg`. -/
def bunchedBimonoidAugGatedAbsorbsStarScope :
    IsSaturatedCongruenceWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidAugGatedEq where
  ofRelation := by
    intro dim cellAlpha cellBeta row
    match row with
    | Or.inl strictRow =>
        match strictRow with
        | .vcompAssoc cellA cellB cellC => exact bunchedBimonoidAugGatedVcompAssoc cellA cellB cellC
        | .vcompUnitLeft cellA => exact bunchedBimonoidAugGatedVcompUnitLeft cellA
        | .vcompUnitRight cellA => exact bunchedBimonoidAugGatedVcompUnitRight cellA
        | .whiskerLeftUnit whiskeringCell innerCell =>
            exact bunchedBimonoidAugGatedWhiskerLeftUnit whiskeringCell innerCell
        | .whiskerRightUnit innerCell whiskeringCell =>
            exact bunchedBimonoidAugGatedWhiskerRightUnit innerCell whiskeringCell
        | .whiskerLeftFunctorial whiskeringCell cellBetaInner cellGamma =>
            exact bunchedBimonoidAugGatedWhiskerLeftFunctorial whiskeringCell cellBetaInner cellGamma
        | .whiskerRightFunctorial cellAlphaInner cellBetaInner whiskeringCell =>
            exact bunchedBimonoidAugGatedWhiskerRightFunctorial cellAlphaInner cellBetaInner
              whiskeringCell
        | .interchange cellAlphaInner cellBetaInner =>
            exact bunchedBimonoidAugGatedInterchange cellAlphaInner cellBetaInner
        | .whiskerAssocLeft whiskP whiskQ innerCell =>
            exact bunchedBimonoidAugGatedWhiskerAssocLeft whiskP whiskQ innerCell
        | .whiskerAssocRight innerCell whiskP whiskQ =>
            exact bunchedBimonoidAugGatedWhiskerAssocRight innerCell whiskP whiskQ
        | .whiskerLeftRightCommute whiskP innerCell whiskQ =>
            exact bunchedBimonoidAugGatedWhiskerLeftRightCommute whiskP innerCell whiskQ
    | Or.inr (Or.inl soundRow) =>
        match soundRow with
        | .multMonadPentagon =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .multMonadRootUnitAssoc =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .addMonadPentagon =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .addMonadRootUnitAssoc =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .comonoidCopentagon =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .comonoidRootCounitCoassoc =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .bialgebraProduct =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .bialgebraCounit =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .bialgebraUnit =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .bialgebraBone =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .commutativity =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .cocommutativity =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .sigmaInvolution =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .sigmaEtaNaturality =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .sigmaEpsNaturality =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
    | Or.inr (Or.inr hexRow) =>
        match hexRow with
        | .yangBaxter =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .muNaturality =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
        | .deltaNaturality =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide),
            fun _ _ => bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)⟩
  vcompCongrLeft := by
    intro dim cellAlpha cellAlpha' cellBeta gatedRel
    match dim with
    | 0 =>
        exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ =>
          congrArg (fun leftWidth => Nat.add leftWidth (bunchedBimonoidEvalAugCell cellBeta))
            (gatedRel.2 rfl rfl)⟩
    | 1 =>
        refine ⟨Iff.intro (fun cleanLeft => ?_) (fun cleanRight => ?_), fun cleanLeft cleanRight => ?_⟩
        · match bunchedBimonoidAugAndSplit cleanLeft with
          | ⟨cleanA, restLeft⟩ =>
              match bunchedBimonoidAugAndSplit restLeft with
              | ⟨cleanB, composeAB⟩ =>
                  refine bunchedBimonoidAugAndJoin (gatedRel.1.mp cleanA)
                    (bunchedBimonoidAugAndJoin cleanB ?_)
                  rw [← gatedRel.2 cleanA (gatedRel.1.mp cleanA)]
                  exact composeAB
        · match bunchedBimonoidAugAndSplit cleanRight with
          | ⟨cleanA', restRight⟩ =>
              match bunchedBimonoidAugAndSplit restRight with
              | ⟨cleanB, composeAB⟩ =>
                  refine bunchedBimonoidAugAndJoin (gatedRel.1.mpr cleanA')
                    (bunchedBimonoidAugAndJoin cleanB ?_)
                  rw [gatedRel.2 (gatedRel.1.mpr cleanA') cleanA']
                  exact composeAB
        · match bunchedBimonoidAugAndSplit cleanLeft, bunchedBimonoidAugAndSplit cleanRight with
          | ⟨cleanA, _⟩, ⟨cleanA', _⟩ =>
              exact congrArg
                (fun leftMatrix => bunchedBimonoidMatMul (bunchedBimonoidEvalAugCell cellBeta)
                  leftMatrix)
                (gatedRel.2 cleanA cleanA')
    | _ + 2 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩
  vcompCongrRight := by
    intro dim cellAlpha cellBeta cellBeta' gatedRel
    match dim with
    | 0 =>
        exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ =>
          congrArg (fun rightWidth => Nat.add (bunchedBimonoidEvalAugCell cellAlpha) rightWidth)
            (gatedRel.2 rfl rfl)⟩
    | 1 =>
        refine ⟨Iff.intro (fun cleanLeft => ?_) (fun cleanRight => ?_), fun cleanLeft cleanRight => ?_⟩
        · match bunchedBimonoidAugAndSplit cleanLeft with
          | ⟨cleanA, restLeft⟩ =>
              match bunchedBimonoidAugAndSplit restLeft with
              | ⟨cleanB, composeAB⟩ =>
                  refine bunchedBimonoidAugAndJoin cleanA
                    (bunchedBimonoidAugAndJoin (gatedRel.1.mp cleanB) ?_)
                  rw [← gatedRel.2 cleanB (gatedRel.1.mp cleanB)]
                  exact composeAB
        · match bunchedBimonoidAugAndSplit cleanRight with
          | ⟨cleanA, restRight⟩ =>
              match bunchedBimonoidAugAndSplit restRight with
              | ⟨cleanB', composeAB⟩ =>
                  refine bunchedBimonoidAugAndJoin cleanA
                    (bunchedBimonoidAugAndJoin (gatedRel.1.mpr cleanB') ?_)
                  rw [gatedRel.2 (gatedRel.1.mpr cleanB') cleanB']
                  exact composeAB
        · match bunchedBimonoidAugAndSplit cleanLeft, bunchedBimonoidAugAndSplit cleanRight with
          | ⟨_, restLeft⟩, ⟨_, restRight⟩ =>
              exact congrArg
                (fun rightMatrix => bunchedBimonoidMatMul rightMatrix
                  (bunchedBimonoidEvalAugCell cellAlpha))
                (gatedRel.2 (bunchedBimonoidAugAndSplit restLeft).1
                  (bunchedBimonoidAugAndSplit restRight).1)
    | _ + 2 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩
  whiskerLeftCongr := by
    intro dim whiskeringCell cellBeta cellBeta' gatedRel
    match dim with
    | 0 =>
        refine ⟨Iff.intro (fun cleanLeft => ?_) (fun cleanRight => ?_), fun cleanLeft cleanRight => ?_⟩
        · match bunchedBimonoidAugAndSplit cleanLeft with
          | ⟨cleanW, cleanB⟩ => exact bunchedBimonoidAugAndJoin cleanW (gatedRel.1.mp cleanB)
        · match bunchedBimonoidAugAndSplit cleanRight with
          | ⟨cleanW, cleanB'⟩ => exact bunchedBimonoidAugAndJoin cleanW (gatedRel.1.mpr cleanB')
        · match bunchedBimonoidAugAndSplit cleanLeft, bunchedBimonoidAugAndSplit cleanRight with
          | ⟨_, cleanB⟩, ⟨_, cleanB'⟩ =>
              exact congrArg
                (bunchedBimonoidAugPointedLeft (bunchedBimonoidAugWordWidth whiskeringCell))
                (gatedRel.2 cleanB cleanB')
    | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩
  whiskerRightCongr := by
    intro dim cellAlpha cellAlpha' whiskeringCell gatedRel
    match dim with
    | 0 =>
        refine ⟨Iff.intro (fun cleanLeft => ?_) (fun cleanRight => ?_), fun cleanLeft cleanRight => ?_⟩
        · match bunchedBimonoidAugAndSplit cleanLeft with
          | ⟨cleanA, cleanW⟩ => exact bunchedBimonoidAugAndJoin (gatedRel.1.mp cleanA) cleanW
        · match bunchedBimonoidAugAndSplit cleanRight with
          | ⟨cleanA', cleanW⟩ => exact bunchedBimonoidAugAndJoin (gatedRel.1.mpr cleanA') cleanW
        · match bunchedBimonoidAugAndSplit cleanLeft, bunchedBimonoidAugAndSplit cleanRight with
          | ⟨cleanA, _⟩, ⟨cleanA', _⟩ =>
              exact congrArg
                (fun cellMatrix => bunchedBimonoidAugPointedRight cellMatrix
                  (bunchedBimonoidAugWordWidth whiskeringCell))
                (gatedRel.2 cleanA cleanA')
    | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩
  idCongr := by
    intro dim cellAlpha cellBeta gatedRel
    match dim with
    | 0 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩
    | 1 =>
        exact ⟨Iff.intro (fun _ => bunchedBimonoidAugCleanOneCell cellBeta)
          (fun _ => bunchedBimonoidAugCleanOneCell cellAlpha), fun _ _ =>
          congrArg (fun width => bunchedBimonoidIdentityMat (Nat.add width 1))
            (gatedRel.2 rfl rfl)⟩
    | _ + 2 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩
  whiskerLeftWhiskerCongr := by
    intro dim whiskerAlpha whiskerAlpha' innerCell gatedRel
    match dim with
    | 0 =>
        refine ⟨Iff.intro (fun cleanLeft => ?_) (fun cleanRight => ?_), fun cleanLeft cleanRight => ?_⟩
        · exact bunchedBimonoidAugAndJoin (bunchedBimonoidAugCleanOneCell whiskerAlpha')
            (bunchedBimonoidAugAndSplit cleanLeft).2
        · exact bunchedBimonoidAugAndJoin (bunchedBimonoidAugCleanOneCell whiskerAlpha)
            (bunchedBimonoidAugAndSplit cleanRight).2
        · exact congrArg
            (fun wireCount => bunchedBimonoidAugPointedLeft wireCount
              (bunchedBimonoidEvalAugCell innerCell))
            (gatedRel.2 rfl rfl)
    | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩
  whiskerRightWhiskerCongr := by
    intro dim innerCell whiskerAlpha whiskerAlpha' gatedRel
    match dim with
    | 0 =>
        refine ⟨Iff.intro (fun cleanLeft => ?_) (fun cleanRight => ?_), fun cleanLeft cleanRight => ?_⟩
        · exact bunchedBimonoidAugAndJoin (bunchedBimonoidAugAndSplit cleanLeft).1
            (bunchedBimonoidAugCleanOneCell whiskerAlpha')
        · exact bunchedBimonoidAugAndJoin (bunchedBimonoidAugAndSplit cleanRight).1
            (bunchedBimonoidAugCleanOneCell whiskerAlpha)
        · exact congrArg
            (bunchedBimonoidAugPointedRight (bunchedBimonoidEvalAugCell innerCell))
            (gatedRel.2 rfl rfl)
    | _ + 1 => exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), fun _ _ => rfl⟩
  refl := fun _ => ⟨Iff.rfl, fun _ _ => rfl⟩
  symm := fun gatedRel =>
    ⟨gatedRel.1.symm, fun cleanRight cleanLeft => (gatedRel.2 cleanLeft cleanRight).symm⟩
  trans := fun gatedLeft gatedRight =>
    ⟨gatedLeft.1.trans gatedRight.1, fun cleanFirst cleanThird =>
      (gatedLeft.2 cleanFirst (gatedLeft.1.mp cleanFirst)).trans
        (gatedRight.2 (gatedLeft.1.mp cleanFirst) cleanThird)⟩

/-- ★★★ **THE FOLD** — star-scope convertibility implies gated augmented equality. -/
theorem bunchedBimonoidAugGatedEqOfStarConv {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (conv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      cellAlpha cellBeta) :
    bunchedBimonoidAugGatedEq cellAlpha cellBeta :=
  SaturatedConvOverWithId.recInto bunchedBimonoidAugGatedAbsorbsStarScope conv

/-! ## The honesty markers -/

/-- ★★★ **ESTABLISHED — the affine-offset semantics absorbs the FULL star scope, composability-gated.**
`= true` records `bunchedBimonoidAugGatedAbsorbsStarScope`: every strict omega-law row (including
`whiskerRightFunctorial` and the Godement interchange, the historical Node-A walls) is absorbed by the
augmented pointed-tensor algebra on Clean instances and by Clean-equivalence on junk instances; the 15 sound
rows and 3 hexagon rows compute; the eleven congruence fields transport.  The invariant the plain `Mat(N)`
semantics cannot see (`bunchedBimonoidAugUnitIntoMuValue`) now folds through EVERY star-scope derivation. -/
def fxBunchedBimonoid_affineOffsetAbsorberShipped : Bool := true

/-! ## The junk-instance falseness witness (WP-PROP r31 additive append — the Clean-gate docstring's
promised machine check, landed) -/

/-- The junk `whiskerRightFunctorial` LEFT leg — the non-composable composite `mu_a ; sigma_a` (interface
`1 != 2`, Clean-false) whiskered right by `a`. -/
def bunchedBimonoidAugJunkFunctorialLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight (CellExpr.vcomp bunchedBimonoidAddMuGen bunchedBimonoidAddSigmaGen)
    bunchedBimonoidAdditiveGen

/-- The junk `whiskerRightFunctorial` RIGHT leg — the whiskers distributed over the junk composite. -/
def bunchedBimonoidAugJunkFunctorialRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen)
    (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)

/-- The junk instance is Clean-FALSE (the gate rejects it). -/
theorem bunchedBimonoidAugJunkFunctorialLeftLegNotClean :
    bunchedBimonoidAugCleanCell bunchedBimonoidAugJunkFunctorialLeftLeg = false := rfl

/-- ★★ **THE PROMISED WITNESS — the strict `whiskerRightFunctorial` row is semantically FALSE on a junk
instance.**  On the Clean-false pair above the two legs have DIFFERENT augmented values (`[[1,0,0,0],
[0,0,0,0],[0,1,1,0],[0,0,0,1]]` vs `[[1,0,0,0],[0,0,0,1],[0,1,1,0],[0,0,0,0]]`, separating at entry
`(1,3)`) — exactly why the r30 absorber must be composability-GATED: an UNgated augmented absorber over the
strict rows is impossible. -/
theorem bunchedBimonoidAugRightFunctorialJunkSeparates :
    bunchedBimonoidEvalAugCell bunchedBimonoidAugJunkFunctorialLeftLeg
      ≠ bunchedBimonoidEvalAugCell bunchedBimonoidAugJunkFunctorialRightLeg := by
  intro valuesEq
  exact absurd
    (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 1 3) valuesEq)
    (by decide)

end FX1Poly.Polygraph.Omega
