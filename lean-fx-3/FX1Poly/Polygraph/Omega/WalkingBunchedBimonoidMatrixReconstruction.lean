import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidSpiderBlockExchange

/-! # Polygraph/Omega/WalkingBunchedBimonoidMatrixReconstruction — the matrix reconstruction kit + the general
matMul associativity + the general-`n` identity unit laws (WP-PROP r5, #2033, the 110-percent grind)

★ **The two Node-A residuals landed at full generality, propext-clean, STRUCTURAL only.**  The r2/r3 kit kept
every matrix in `List.range` / `List.replicate` normal form to dodge `List (List Nat)` extensionality; the #2033
star (the diagram-to-matrix retraction) makes it unavoidable.  This file ships the genuinely-new content:

  * **The reconstruction kit** — a list-equals-the-range-map-of-its-own-gets induction (`bunchedBimonoidRange
    SuccCons`, `...NatListRebuild`, `...RowListRebuild`, `...MatReconstruct`), all cons/`Nat`-structural, hitting
    ONLY the shipped `List.range` reindexing kit and the definitional getter arms.  No Init `getD` / `range_succ`
    / `length_map` (all leak `propext`).
  * **The get-of-range-map readers** — `bunchedBimonoidNatListGetRangeMap`, `...RowListGetRangeMap`: the
    in-range read of a `List.range`-generated column / row is the generating function at the index.
  * **`bunchedBimonoidMatMulEntryRead`** — the matMul entry exposed as a contraction sum (needs only the two
    in-range reads; wf-free).
  * **The finite-sum Fubini kit** — `bunchedBimonoidAddMul` / `...MulAdd` / `...MulAssoc` (hand-rolled; Init's
    `Nat.add_mul` leaks `propext`), `...SumMulRight` / `...SumMulLeft` / `...SumMapAdd`, and THE double-induction
    `bunchedBimonoidNatListSumSwap` (the Fubini swap).
  * **Node A residual (1) — `bunchedBimonoidMatMulAssoc`** — general `matMul` associativity for composable
    matrices, assembled pointwise via the Fubini kit (no reconstruction needed; the two contraction index sets
    coincide under composability, so a clean Fubini with fixed ranges).
  * **Node A residual (2) — `bunchedBimonoidIdentity{Right,Left}Unit`** — the general-`n` identity unit laws,
    via the reconstruction + the delta-collapse.

Raw Lean 4 + Init; STRUCTURAL only (no `WellFounded.fix`); ASCII-only.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # THE RECONSTRUCTION KIT — list = range-map of its own gets (cons-structural)
    # =========================================================================================
-/

/-- ★ **The range successor CONS** `List.range (count+1) = 0 :: (List.range count).map (· + 1)` — the front-cons
range primitive the reconstruction needs (the shipped kit has only the SNOC `bunchedBimonoidRangeSuccSnoc`, the
wrong end for a cons-peel).  Structural on `count` via the shipped snoc + map-append distributivity; propext-clean
(Init's `List.range_succ` leaks). -/
theorem bunchedBimonoidRangeSuccCons : ∀ (count : Nat),
    List.range (count + 1) = 0 :: (List.range count).map (fun index => index + 1)
  | 0 => rfl
  | count + 1 => by
      have ih := bunchedBimonoidRangeSuccCons count
      calc List.range (count + 2)
          = List.range (count + 1) ++ [count + 1] := bunchedBimonoidRangeSuccSnoc (count + 1)
        _ = (0 :: (List.range count).map (fun index => index + 1)) ++ [count + 1] := by rw [ih]
        _ = 0 :: ((List.range count).map (fun index => index + 1) ++ [count + 1]) := rfl
        _ = 0 :: ((List.range count).map (fun index => index + 1)
              ++ [count].map (fun index => index + 1)) := rfl
        _ = 0 :: (List.range count ++ [count]).map (fun index => index + 1) := by
              rw [bunchedBimonoidMapAppendDistrib]
        _ = 0 :: (List.range (count + 1)).map (fun index => index + 1) := by
              rw [bunchedBimonoidRangeSuccSnoc count]

/-- ★ **The `List Nat` rebuild** `(List.range row.length).map (natListGet row) = row` — a `List Nat` is the
range-map of its own gets.  Structural on the row (cons-peel), via the range-succ-cons + map-map fusion + the
definitional getter arms; propext-clean. -/
theorem bunchedBimonoidNatListRebuild : ∀ (row : List Nat),
    (List.range row.length).map (fun colIndex => bunchedBimonoidNatListGet row colIndex) = row
  | [] => rfl
  | head :: tail => by
      show (List.range (tail.length + 1)).map
          (fun colIndex => bunchedBimonoidNatListGet (head :: tail) colIndex) = head :: tail
      rw [bunchedBimonoidRangeSuccCons tail.length]
      show bunchedBimonoidNatListGet (head :: tail) 0
          :: ((List.range tail.length).map (fun index => index + 1)).map
              (fun colIndex => bunchedBimonoidNatListGet (head :: tail) colIndex)
        = head :: tail
      rw [bunchedBimonoidMapMapFusion]
      show head :: (List.range tail.length).map
          (fun index => bunchedBimonoidNatListGet (head :: tail) (index + 1)) = head :: tail
      exact congrArg (head :: ·) (bunchedBimonoidNatListRebuild tail)

/-- ★ **The `List (List Nat)` rebuild** `(List.range rows.length).map (rowListGet rows) = rows` — a list of rows
is the range-map of its own row-gets.  Same cons-structural proof as `bunchedBimonoidNatListRebuild`. -/
theorem bunchedBimonoidRowListRebuild : ∀ (rows : List (List Nat)),
    (List.range rows.length).map (fun rowIndex => bunchedBimonoidRowListGet rows rowIndex) = rows
  | [] => rfl
  | head :: tail => by
      show (List.range (tail.length + 1)).map
          (fun rowIndex => bunchedBimonoidRowListGet (head :: tail) rowIndex) = head :: tail
      rw [bunchedBimonoidRangeSuccCons tail.length]
      show bunchedBimonoidRowListGet (head :: tail) 0
          :: ((List.range tail.length).map (fun index => index + 1)).map
              (fun rowIndex => bunchedBimonoidRowListGet (head :: tail) rowIndex)
        = head :: tail
      rw [bunchedBimonoidMapMapFusion]
      show head :: (List.range tail.length).map
          (fun index => bunchedBimonoidRowListGet (head :: tail) (index + 1)) = head :: tail
      exact congrArg (head :: ·) (bunchedBimonoidRowListRebuild tail)

/-! # =========================================================================================
    # THE GET-OF-RANGE-MAP READERS + THE MATRIX RECONSTRUCTION
    # =========================================================================================
-/

/-- **The in-range read of a range-generated column** `natListGet ((range count).map transform) index =
transform index` for `index < count`.  Structural on `count` via the range-succ-cons; propext-clean. -/
theorem bunchedBimonoidNatListGetRangeMap : ∀ (count : Nat) (transform : Nat → Nat) (index : Nat),
    index < count →
    bunchedBimonoidNatListGet ((List.range count).map transform) index = transform index
  | 0, _, _, below => absurd below (Nat.not_lt_zero _)
  | count + 1, transform, 0, _ => by
      rw [bunchedBimonoidRangeSuccCons count]
      show bunchedBimonoidNatListGet
          (transform 0 :: ((List.range count).map (fun index => index + 1)).map transform) 0 = transform 0
      rfl
  | count + 1, transform, index + 1, below => by
      rw [bunchedBimonoidRangeSuccCons count]
      show bunchedBimonoidNatListGet
          (transform 0 :: ((List.range count).map (fun i => i + 1)).map transform) (index + 1)
        = transform (index + 1)
      rw [bunchedBimonoidMapMapFusion]
      show bunchedBimonoidNatListGet ((List.range count).map (fun i => transform (i + 1))) index
        = transform (index + 1)
      exact bunchedBimonoidNatListGetRangeMap count (fun i => transform (i + 1)) index
        (Nat.lt_of_succ_lt_succ below)

/-- **The in-range read of a range-generated row list** `rowListGet ((range count).map transform) index =
transform index` for `index < count`.  Structural on `count`; propext-clean. -/
theorem bunchedBimonoidRowListGetRangeMap : ∀ (count : Nat) (transform : Nat → List Nat) (index : Nat),
    index < count →
    bunchedBimonoidRowListGet ((List.range count).map transform) index = transform index
  | 0, _, _, below => absurd below (Nat.not_lt_zero _)
  | count + 1, transform, 0, _ => by
      rw [bunchedBimonoidRangeSuccCons count]
      show bunchedBimonoidRowListGet
          (transform 0 :: ((List.range count).map (fun index => index + 1)).map transform) 0 = transform 0
      rfl
  | count + 1, transform, index + 1, below => by
      rw [bunchedBimonoidRangeSuccCons count]
      show bunchedBimonoidRowListGet
          (transform 0 :: ((List.range count).map (fun i => i + 1)).map transform) (index + 1)
        = transform (index + 1)
      rw [bunchedBimonoidMapMapFusion]
      show bunchedBimonoidRowListGet ((List.range count).map (fun i => transform (i + 1))) index
        = transform (index + 1)
      exact bunchedBimonoidRowListGetRangeMap count (fun i => transform (i + 1)) index
        (Nat.lt_of_succ_lt_succ below)

/-- ★★ **THE MATRIX RECONSTRUCTION** `(range M.rows).map (fun i => (range M.cols).map (matEntryAt M i)) =
M.entries` for well-formed `M` — Node A residual (2)'s named target, exactly.  The double range-map of the entry
function rebuilds the entries list.  Via the row-rebuild (outer) with the nat-rebuild (inner), aligning `M.cols`
with each row's actual length through well-formedness; propext-clean. -/
theorem bunchedBimonoidMatReconstruct (matrix : BunchedBimonoidMat)
    (wf : bunchedBimonoidMatWellFormed matrix) :
    (List.range matrix.rows).map (fun rowIndex =>
      (List.range matrix.cols).map (fun colIndex => bunchedBimonoidMatEntryAt matrix rowIndex colIndex))
      = matrix.entries := by
  rw [← wf.1]
  refine Eq.trans
    (bunchedBimonoidRangeMapCongr _ _ matrix.entries.length ?_)
    (bunchedBimonoidRowListRebuild matrix.entries)
  intro rowIndex rowBelow
  have rowLen : (bunchedBimonoidRowListGet matrix.entries rowIndex).length = matrix.cols :=
    wf.2 rowIndex (wf.1 ▸ rowBelow)
  show (List.range matrix.cols).map (fun colIndex => bunchedBimonoidMatEntryAt matrix rowIndex colIndex)
    = bunchedBimonoidRowListGet matrix.entries rowIndex
  rw [← rowLen]
  exact bunchedBimonoidNatListRebuild (bunchedBimonoidRowListGet matrix.entries rowIndex)

/-! # =========================================================================================
    # THE FINITE-SUM FUBINI KIT (all propext-clean; Init's `add_mul` / `mul_assoc` leak)
    # =========================================================================================
-/

/-- **Middle-four interchange** `(w + x) + (y + z) = (w + y) + (x + z)` — the commutative-monoid rearrangement.
Clean (only `add_assoc` / `add_comm`). -/
theorem bunchedBimonoidAddMiddleFour (w x y z : Nat) : (w + x) + (y + z) = (w + y) + (x + z) := by
  rw [Nat.add_assoc w x (y + z), ← Nat.add_assoc x y z, Nat.add_comm x y, Nat.add_assoc y x z,
    ← Nat.add_assoc w y (x + z)]

/-- **Right distributivity** `(a + b) * c = a * c + b * c` — hand-rolled (Init's `Nat.add_mul` leaks `propext`).
Structural on `c` via `Nat.mul_succ` (definitional) + the middle-four interchange; clean. -/
theorem bunchedBimonoidAddMul : ∀ (a b c : Nat), (a + b) * c = a * c + b * c
  | _, _, 0 => rfl
  | a, b, c + 1 => by
      show (a + b) * c + (a + b) = a * c + a + (b * c + b)
      rw [bunchedBimonoidAddMul a b c]
      exact bunchedBimonoidAddMiddleFour (a * c) (b * c) a b

/-- **Left distributivity** `a * (x + y) = a * x + a * y` — hand-rolled (Init's `Nat.mul_add` leaks `propext`).
Structural on `y`; clean. -/
theorem bunchedBimonoidMulAdd : ∀ (a x y : Nat), a * (x + y) = a * x + a * y
  | _, _, 0 => rfl
  | a, x, y + 1 => by
      show a * (x + y) + a = a * x + (a * y + a)
      rw [bunchedBimonoidMulAdd a x y, Nat.add_assoc]

/-- **Multiplicative associativity** `a * b * c = a * (b * c)` — hand-rolled (Init's `Nat.mul_assoc` leaks
`propext`).  Structural on `c` via left distributivity; clean. -/
theorem bunchedBimonoidMulAssoc : ∀ (a b c : Nat), a * b * c = a * (b * c)
  | _, _, 0 => rfl
  | a, b, c + 1 => by
      show a * b * c + a * b = a * (b * c + b)
      rw [bunchedBimonoidMulAdd a (b * c) b, bunchedBimonoidMulAssoc a b c]

/-- **Zero on the left of `*`** `0 * c = 0` — hand-rolled (Nat's `mul` recurses on the SECOND argument, so this
is not `rfl`).  Structural on `c`; clean. -/
theorem bunchedBimonoidNatZeroMul : ∀ (c : Nat), 0 * c = 0
  | 0 => rfl
  | c + 1 => by
      show 0 * c + 0 = 0
      rw [Nat.add_zero]
      exact bunchedBimonoidNatZeroMul c

/-- **Sum scales on the right** `natListSum xs * c = natListSum (xs.map (· * c))` — the right-distribution of a
scalar over a finite sum.  Structural on the list via right distributivity; clean. -/
theorem bunchedBimonoidSumMulRight : ∀ (xs : List Nat) (multiplier : Nat),
    bunchedBimonoidNatListSum xs * multiplier
      = bunchedBimonoidNatListSum (xs.map (fun element => element * multiplier))
  | [], multiplier => bunchedBimonoidNatZeroMul multiplier
  | element :: xs, multiplier => by
      show (element + bunchedBimonoidNatListSum xs) * multiplier
        = element * multiplier + bunchedBimonoidNatListSum (xs.map (fun element => element * multiplier))
      rw [bunchedBimonoidAddMul element (bunchedBimonoidNatListSum xs) multiplier,
        bunchedBimonoidSumMulRight xs multiplier]

/-- **Sum scales on the left** `c * natListSum xs = natListSum (xs.map (c * ·))` — the left-distribution.
Structural on the list via left distributivity; clean. -/
theorem bunchedBimonoidSumMulLeft : ∀ (multiplier : Nat) (xs : List Nat),
    multiplier * bunchedBimonoidNatListSum xs
      = bunchedBimonoidNatListSum (xs.map (fun element => multiplier * element))
  | _, [] => by rfl
  | multiplier, element :: xs => by
      show multiplier * (element + bunchedBimonoidNatListSum xs)
        = multiplier * element + bunchedBimonoidNatListSum (xs.map (fun element => multiplier * element))
      rw [bunchedBimonoidMulAdd multiplier element (bunchedBimonoidNatListSum xs),
        bunchedBimonoidSumMulLeft multiplier xs]

/-- **Sum splits over a pointwise add** `natListSum (l.map (fun x => f x + g x)) = natListSum (l.map f) +
natListSum (l.map g)`.  Structural on the list via the middle-four interchange; clean. -/
theorem bunchedBimonoidSumMapAdd {source : Type} (firstMap secondMap : source → Nat) :
    ∀ (elements : List source),
      bunchedBimonoidNatListSum (elements.map (fun element => firstMap element + secondMap element))
        = bunchedBimonoidNatListSum (elements.map firstMap)
          + bunchedBimonoidNatListSum (elements.map secondMap)
  | [] => rfl
  | element :: elements => by
      show (firstMap element + secondMap element)
          + bunchedBimonoidNatListSum (elements.map (fun element => firstMap element + secondMap element))
        = (firstMap element + bunchedBimonoidNatListSum (elements.map firstMap))
          + (secondMap element + bunchedBimonoidNatListSum (elements.map secondMap))
      rw [bunchedBimonoidSumMapAdd firstMap secondMap elements]
      exact bunchedBimonoidAddMiddleFour (firstMap element) (secondMap element)
        (bunchedBimonoidNatListSum (elements.map firstMap))
        (bunchedBimonoidNatListSum (elements.map secondMap))

/-- **Sum of a range-map to zero is zero** `natListSum (l.map (fun _ => 0)) = 0`.  Structural on the list;
clean. -/
theorem bunchedBimonoidNatListSumMapZero {source : Type} : ∀ (elements : List source),
    bunchedBimonoidNatListSum (elements.map (fun _ => 0)) = 0
  | [] => rfl
  | _ :: elements => by
      show 0 + bunchedBimonoidNatListSum (elements.map (fun _ => 0)) = 0
      rw [bunchedBimonoidNatListSumMapZero elements]

/-- **The range-sum successor** `natListSum ((range (m+1)).map g) = natListSum ((range m).map g) + g m` — the sum
peels its last (snoc) index.  Via the shipped range-succ-snoc + the finite-sum append law; clean. -/
theorem bunchedBimonoidSumRangeSucc (g : Nat → Nat) (m : Nat) :
    bunchedBimonoidNatListSum ((List.range (m + 1)).map g)
      = bunchedBimonoidNatListSum ((List.range m).map g) + g m := by
  rw [bunchedBimonoidRangeSuccSnoc, bunchedBimonoidMapAppendDistrib, bunchedBimonoidNatListSumAppend]
  rfl

/-- ★★ **THE FUBINI SWAP** — the double-sum over `(range m) x (range n)` is symmetric:
`natListSum ((range m).map (fun k => natListSum ((range n).map (fun p => f p k))))
  = natListSum ((range n).map (fun p => natListSum ((range m).map (fun k => f p k))))`.
Structural on `m` via the range-sum successor + `sumMapAdd` + the IH; clean. -/
theorem bunchedBimonoidNatListSumSwap (n : Nat) (f : Nat → Nat → Nat) : ∀ (m : Nat),
    bunchedBimonoidNatListSum ((List.range m).map
        (fun outerK => bunchedBimonoidNatListSum ((List.range n).map (fun innerP => f innerP outerK))))
      = bunchedBimonoidNatListSum ((List.range n).map
        (fun outerP => bunchedBimonoidNatListSum ((List.range m).map (fun innerK => f outerP innerK))))
  | 0 => by
      exact (bunchedBimonoidNatListSumMapZero (List.range n)).symm
  | m + 1 => by
      rw [bunchedBimonoidSumRangeSucc
        (fun outerK => bunchedBimonoidNatListSum ((List.range n).map (fun innerP => f innerP outerK))) m]
      rw [bunchedBimonoidNatListSumSwap n f m]
      rw [bunchedBimonoidRangeMapCongr
          (fun outerP => bunchedBimonoidNatListSum ((List.range (m + 1)).map (fun innerK => f outerP innerK)))
          (fun outerP => bunchedBimonoidNatListSum ((List.range m).map (fun innerK => f outerP innerK))
            + f outerP m)
          n
          (fun outerP _ => bunchedBimonoidSumRangeSucc (fun innerK => f outerP innerK) m)]
      rw [bunchedBimonoidSumMapAdd
          (fun outerP => bunchedBimonoidNatListSum ((List.range m).map (fun innerK => f outerP innerK)))
          (fun outerP => f outerP m) (List.range n)]

/-- ★★ **THE matMul ENTRY READ** `matEntryAt (matMul later earlier) i j = natListSum ((range earlier.rows).map
(fun k => matEntryAt later i k * matEntryAt earlier k j))` for `i < later.rows`, `j < earlier.cols`.  wf-free —
both reads land in range via the two range-map getters. -/
theorem bunchedBimonoidMatMulEntryRead (later earlier : BunchedBimonoidMat)
    (rowIndex colIndex : Nat) (rowBelow : rowIndex < later.rows) (colBelow : colIndex < earlier.cols) :
    bunchedBimonoidMatEntryAt (bunchedBimonoidMatMul later earlier) rowIndex colIndex
      = bunchedBimonoidNatListSum ((List.range earlier.rows).map (fun contractionIndex =>
          bunchedBimonoidMatEntryAt later rowIndex contractionIndex
            * bunchedBimonoidMatEntryAt earlier contractionIndex colIndex)) := by
  show bunchedBimonoidNatListGet
      (bunchedBimonoidRowListGet
        ((List.range later.rows).map (fun rowIx =>
          (List.range earlier.cols).map (fun colIx =>
            bunchedBimonoidNatListSum ((List.range earlier.rows).map (fun k =>
              bunchedBimonoidMatEntryAt later rowIx k * bunchedBimonoidMatEntryAt earlier k colIx)))))
        rowIndex)
      colIndex
    = bunchedBimonoidNatListSum ((List.range earlier.rows).map (fun contractionIndex =>
        bunchedBimonoidMatEntryAt later rowIndex contractionIndex
          * bunchedBimonoidMatEntryAt earlier contractionIndex colIndex))
  rw [bunchedBimonoidRowListGetRangeMap later.rows
      (fun rowIx => (List.range earlier.cols).map (fun colIx =>
        bunchedBimonoidNatListSum ((List.range earlier.rows).map (fun k =>
          bunchedBimonoidMatEntryAt later rowIx k * bunchedBimonoidMatEntryAt earlier k colIx))))
      rowIndex rowBelow]
  rw [bunchedBimonoidNatListGetRangeMap earlier.cols
      (fun colIx => bunchedBimonoidNatListSum ((List.range earlier.rows).map (fun k =>
        bunchedBimonoidMatEntryAt later rowIndex k * bunchedBimonoidMatEntryAt earlier k colIx)))
      colIndex colBelow]

/-! ## The reconstruction truth-probes (concrete matrices, `rfl` FIRST per the recon) -/

/-- Truth-probe: reconstruction on a concrete `2 x 3` matrix is `rfl` (the double range-map of the entry function
rebuilds the entries). -/
theorem bunchedBimonoidMatReconstructProbeTwoThree :
    (List.range 2).map (fun rowIndex => (List.range 3).map (fun colIndex =>
      bunchedBimonoidMatEntryAt { rows := 2, cols := 3, entries := [[1, 2, 3], [4, 5, 6]] } rowIndex colIndex))
      = [[1, 2, 3], [4, 5, 6]] := rfl

/-- Truth-probe: the matMul entry read on a concrete product is `rfl`. -/
theorem bunchedBimonoidMatMulEntryReadProbe :
    bunchedBimonoidMatEntryAt (bunchedBimonoidMatMul
      { rows := 2, cols := 2, entries := [[1, 2], [3, 4]] }
      { rows := 2, cols := 2, entries := [[5, 6], [7, 8]] }) 0 1
      = bunchedBimonoidNatListSum ((List.range 2).map (fun k =>
          bunchedBimonoidMatEntryAt { rows := 2, cols := 2, entries := [[1, 2], [3, 4]] } 0 k
            * bunchedBimonoidMatEntryAt { rows := 2, cols := 2, entries := [[5, 6], [7, 8]] } k 1)) := rfl

/-! # =========================================================================================
    # NODE A residual (1) — GENERAL matMul ASSOCIATIVITY (the 3-factor Fubini)
    # =========================================================================================
-/

/-- ★★★ **NODE A residual (1) — general `matMul` associativity.**  `matMul (matMul A B) C = matMul A (matMul B
C)` for composable matrices (`B.cols = C.rows`).  Both sides already carry the SAME declared `rows := A.rows`,
`cols := C.cols`, so the equality reduces (structure eta) to the entries, assembled pointwise via two range-map
congruences down to the per-`(i,j)` 3-factor identity; that identity is `matMulEntryRead` (expose the nested
products as sums) + right/left scalar distribution + `mulAssoc` + THE Fubini swap.  Under composability the two
contraction index sets coincide, so no zero-tail split — the clean Fubini.  No reconstruction needed; wf-free. -/
theorem bunchedBimonoidMatMulAssoc (matA matB matC : BunchedBimonoidMat)
    (composeBC : matB.cols = matC.rows) :
    bunchedBimonoidMatMul (bunchedBimonoidMatMul matA matB) matC
      = bunchedBimonoidMatMul matA (bunchedBimonoidMatMul matB matC) := by
  have entriesEq :
      (bunchedBimonoidMatMul (bunchedBimonoidMatMul matA matB) matC).entries
        = (bunchedBimonoidMatMul matA (bunchedBimonoidMatMul matB matC)).entries := by
    show (List.range matA.rows).map (fun rowIndex =>
          (List.range matC.cols).map (fun colIndex =>
            bunchedBimonoidNatListSum ((List.range matC.rows).map (fun k =>
              bunchedBimonoidMatEntryAt (bunchedBimonoidMatMul matA matB) rowIndex k
                * bunchedBimonoidMatEntryAt matC k colIndex))))
      = (List.range matA.rows).map (fun rowIndex =>
          (List.range matC.cols).map (fun colIndex =>
            bunchedBimonoidNatListSum ((List.range matB.rows).map (fun p =>
              bunchedBimonoidMatEntryAt matA rowIndex p
                * bunchedBimonoidMatEntryAt (bunchedBimonoidMatMul matB matC) p colIndex))))
    refine bunchedBimonoidRangeMapCongr _ _ matA.rows (fun rowIndex rowBelow => ?_)
    refine bunchedBimonoidRangeMapCongr _ _ matC.cols (fun colIndex colBelow => ?_)
    have lhsCommon :
        bunchedBimonoidNatListSum ((List.range matC.rows).map (fun k =>
            bunchedBimonoidMatEntryAt (bunchedBimonoidMatMul matA matB) rowIndex k
              * bunchedBimonoidMatEntryAt matC k colIndex))
          = bunchedBimonoidNatListSum ((List.range matC.rows).map (fun k =>
            bunchedBimonoidNatListSum ((List.range matB.rows).map (fun p =>
              bunchedBimonoidMatEntryAt matA rowIndex p
                * (bunchedBimonoidMatEntryAt matB p k * bunchedBimonoidMatEntryAt matC k colIndex))))) :=
      congrArg bunchedBimonoidNatListSum
        (bunchedBimonoidRangeMapCongr _ _ matC.rows (fun k kBelow => by
          have kb2 : k < matB.cols := by rw [composeBC]; exact kBelow
          rw [bunchedBimonoidMatMulEntryRead matA matB rowIndex k rowBelow kb2,
            bunchedBimonoidSumMulRight, bunchedBimonoidMapMapFusion]
          exact congrArg bunchedBimonoidNatListSum
            (bunchedBimonoidRangeMapCongr _ _ matB.rows (fun p _ =>
              bunchedBimonoidMulAssoc (bunchedBimonoidMatEntryAt matA rowIndex p)
                (bunchedBimonoidMatEntryAt matB p k) (bunchedBimonoidMatEntryAt matC k colIndex)))))
    have rhsCommon :
        bunchedBimonoidNatListSum ((List.range matB.rows).map (fun p =>
            bunchedBimonoidMatEntryAt matA rowIndex p
              * bunchedBimonoidMatEntryAt (bunchedBimonoidMatMul matB matC) p colIndex))
          = bunchedBimonoidNatListSum ((List.range matB.rows).map (fun p =>
            bunchedBimonoidNatListSum ((List.range matC.rows).map (fun k =>
              bunchedBimonoidMatEntryAt matA rowIndex p
                * (bunchedBimonoidMatEntryAt matB p k * bunchedBimonoidMatEntryAt matC k colIndex))))) :=
      congrArg bunchedBimonoidNatListSum
        (bunchedBimonoidRangeMapCongr _ _ matB.rows (fun p pBelow => by
          rw [bunchedBimonoidMatMulEntryRead matB matC p colIndex pBelow colBelow,
            bunchedBimonoidSumMulLeft, bunchedBimonoidMapMapFusion]))
    rw [lhsCommon, rhsCommon]
    exact bunchedBimonoidNatListSumSwap matB.rows
      (fun p k => bunchedBimonoidMatEntryAt matA rowIndex p
        * (bunchedBimonoidMatEntryAt matB p k * bunchedBimonoidMatEntryAt matC k colIndex))
      matC.rows
  calc bunchedBimonoidMatMul (bunchedBimonoidMatMul matA matB) matC
      = BunchedBimonoidMat.mk matA.rows matC.cols
          (bunchedBimonoidMatMul (bunchedBimonoidMatMul matA matB) matC).entries := rfl
    _ = BunchedBimonoidMat.mk matA.rows matC.cols
          (bunchedBimonoidMatMul matA (bunchedBimonoidMatMul matB matC)).entries := by rw [entriesEq]
    _ = bunchedBimonoidMatMul matA (bunchedBimonoidMatMul matB matC) := rfl

/-- Truth-probe: general associativity specialises to a concrete non-square triple on the nose (`rfl` via the
proved general lemma applied to closed matrices — the composability hypotheses discharge by `rfl`). -/
theorem bunchedBimonoidMatMulAssocProbeNonSquare :
    bunchedBimonoidMatMul (bunchedBimonoidMatMul
        { rows := 2, cols := 3, entries := [[1, 2, 3], [4, 5, 6]] }
        { rows := 3, cols := 2, entries := [[1, 0], [0, 1], [1, 1]] })
        { rows := 2, cols := 2, entries := [[2, 1], [1, 2]] }
      = bunchedBimonoidMatMul { rows := 2, cols := 3, entries := [[1, 2, 3], [4, 5, 6]] }
        (bunchedBimonoidMatMul { rows := 3, cols := 2, entries := [[1, 0], [0, 1], [1, 1]] }
          { rows := 2, cols := 2, entries := [[2, 1], [1, 2]] }) :=
  bunchedBimonoidMatMulAssoc _ _ _ rfl

/-! # =========================================================================================
    # NODE A residual (2) — THE GENERAL-`n` IDENTITY UNIT LAWS (the delta collapse)
    # =========================================================================================

The `BEq Nat` instance is `instBEqOfDecidableEq`, so `k == j` is `decide (k = j)` (NOT `Nat.beq`); the delta
reasoning goes through `decide` + the two hand-rolled Decidable readers (propext-clean — a `Decidable`-case + an
`absurd`, no `decide_eq_true_eq` which leaks `propext`). -/

/-- **`decide p = true` from a proof of `p`** — hand-rolled (Init's `decide_eq_true_eq` leaks `propext`).  A
`Decidable`-case: `isTrue` is `rfl`, `isFalse` is absurd. -/
theorem bunchedBimonoidDecideEqTrue {statement : Prop} [instDecide : Decidable statement]
    (holds : statement) : decide statement = true :=
  match instDecide with
  | isTrue _ => rfl
  | isFalse doesNotHold => absurd holds doesNotHold

/-- **`decide p = false` from a refutation of `p`** — hand-rolled, `Decidable`-case; propext-clean. -/
theorem bunchedBimonoidDecideEqFalse {statement : Prop} [instDecide : Decidable statement]
    (refutes : ¬ statement) : decide statement = false :=
  match instDecide with
  | isTrue holds => absurd holds refutes
  | isFalse _ => rfl

/-- **`c * 1 = c`** — hand-rolled (Nat's `mul` recurses on the second argument, so this is not `rfl`).  Structural
on `c`; clean. -/
theorem bunchedBimonoidNatMulOne : ∀ (value : Nat), value * 1 = value
  | 0 => rfl
  | value + 1 => by show value * 1 + 1 = value + 1; rw [bunchedBimonoidNatMulOne value]

/-- **`1 * c = c`** — hand-rolled; structural on `c`; clean. -/
theorem bunchedBimonoidNatOneMul : ∀ (value : Nat), 1 * value = value
  | 0 => rfl
  | value + 1 => by show 1 * value + 1 = value + 1; rw [bunchedBimonoidNatOneMul value]

/-- **The right-factor delta multiplier collapses to the coefficient** `c * (if k == j then 1 else 0) = c` when
`k = j`.  Via `if_pos` (driven by `decide`) + `mul_one`. -/
theorem bunchedBimonoidDeltaMulRightEq (coefficient contractionIndex targetIndex : Nat)
    (indicesAgree : contractionIndex = targetIndex) :
    coefficient * (if contractionIndex == targetIndex then 1 else 0) = coefficient := by
  rw [if_pos (show (contractionIndex == targetIndex) = true from bunchedBimonoidDecideEqTrue indicesAgree)]
  exact bunchedBimonoidNatMulOne coefficient

/-- **The right-factor delta multiplier collapses to zero** `c * (if k == j then 1 else 0) = 0` when `k != j`.  Via
`if_neg` (driven by `decide`); `c * 0 = 0` is definitional. -/
theorem bunchedBimonoidDeltaMulRightNe (coefficient contractionIndex targetIndex : Nat)
    (indicesDiffer : contractionIndex ≠ targetIndex) :
    coefficient * (if contractionIndex == targetIndex then 1 else 0) = 0 := by
  have condFalse : (contractionIndex == targetIndex) = false := bunchedBimonoidDecideEqFalse indicesDiffer
  rw [if_neg (by rw [condFalse]; exact Bool.false_ne_true)]
  rfl

/-- **The left-factor delta multiplier collapses to the coefficient** `(if i == k then 1 else 0) * c = c` when
`i = k`.  Via `if_pos` + `one_mul`. -/
theorem bunchedBimonoidDeltaMulLeftEq (coefficient rowIndex contractionIndex : Nat)
    (indicesAgree : rowIndex = contractionIndex) :
    (if rowIndex == contractionIndex then 1 else 0) * coefficient = coefficient := by
  rw [if_pos (show (rowIndex == contractionIndex) = true from bunchedBimonoidDecideEqTrue indicesAgree)]
  exact bunchedBimonoidNatOneMul coefficient

/-- **The left-factor delta multiplier collapses to zero** `(if i == k then 1 else 0) * c = 0` when `i != k`. -/
theorem bunchedBimonoidDeltaMulLeftNe (coefficient rowIndex contractionIndex : Nat)
    (indicesDiffer : rowIndex ≠ contractionIndex) :
    (if rowIndex == contractionIndex then 1 else 0) * coefficient = 0 := by
  have condFalse : (rowIndex == contractionIndex) = false := bunchedBimonoidDecideEqFalse indicesDiffer
  rw [if_neg (by rw [condFalse]; exact Bool.false_ne_true)]
  show 0 * coefficient = 0
  exact bunchedBimonoidNatZeroMul coefficient

/-- ★ **The identity matrix entry is the Kronecker delta** `matEntryAt (identityMat n) k j = if k == j then 1
else 0` for `k < n`, `j < n`.  Via the two in-range range-map readers (no `beq` reasoning — pure structural
gets). -/
theorem bunchedBimonoidIdentityMatEntry (dimension rowIndex colIndex : Nat)
    (rowBelow : rowIndex < dimension) (colBelow : colIndex < dimension) :
    bunchedBimonoidMatEntryAt (bunchedBimonoidIdentityMat dimension) rowIndex colIndex
      = if rowIndex == colIndex then 1 else 0 := by
  show bunchedBimonoidNatListGet
      (bunchedBimonoidRowListGet
        ((List.range dimension).map (fun r => (List.range dimension).map (fun c => if r == c then 1 else 0)))
        rowIndex)
      colIndex
    = if rowIndex == colIndex then 1 else 0
  rw [bunchedBimonoidRowListGetRangeMap dimension
      (fun r => (List.range dimension).map (fun c => if r == c then 1 else 0)) rowIndex rowBelow]
  rw [bunchedBimonoidNatListGetRangeMap dimension
      (fun c => if rowIndex == c then 1 else 0) colIndex colBelow]

/-- ★★ **THE RIGHT DELTA COLLAPSE** `natListSum ((range n).map (fun k => coeffAt k * (if k == j then 1 else 0)))
= coeffAt j` for `j < n` — the sum against a delta on the right factor picks out the coefficient at the target.
Structural on `n` via the range-sum successor; the last index either IS the target (tail is the coefficient, head
all-off is zero) or is not (tail zero, head recurses).  Propext-clean. -/
theorem bunchedBimonoidDeltaCollapseRight (coeffAt : Nat → Nat) : ∀ (dimension targetIndex : Nat),
    targetIndex < dimension →
    bunchedBimonoidNatListSum ((List.range dimension).map (fun contractionIndex =>
        coeffAt contractionIndex * (if contractionIndex == targetIndex then 1 else 0)))
      = coeffAt targetIndex
  | 0, _, below => absurd below (Nat.not_lt_zero _)
  | dimension + 1, targetIndex, targetBelow => by
      rw [bunchedBimonoidSumRangeSucc
        (fun contractionIndex => coeffAt contractionIndex * (if contractionIndex == targetIndex then 1 else 0))
        dimension]
      match Nat.lt_or_ge targetIndex dimension with
      | Or.inl targetLtDim =>
          rw [bunchedBimonoidDeltaCollapseRight coeffAt dimension targetIndex targetLtDim,
            bunchedBimonoidDeltaMulRightNe (coeffAt dimension) dimension targetIndex
              (Nat.ne_of_lt targetLtDim).symm]
          rfl
      | Or.inr targetGeDim =>
          have targetEqDim : targetIndex = dimension :=
            Nat.le_antisymm (Nat.le_of_lt_succ targetBelow) targetGeDim
          have headZero : bunchedBimonoidNatListSum ((List.range dimension).map (fun contractionIndex =>
              coeffAt contractionIndex * (if contractionIndex == targetIndex then 1 else 0))) = 0 := by
            rw [congrArg bunchedBimonoidNatListSum
              (bunchedBimonoidRangeMapCongr
                (fun contractionIndex =>
                  coeffAt contractionIndex * (if contractionIndex == targetIndex then 1 else 0))
                (fun _ => 0) dimension
                (fun contractionIndex indexBelow =>
                  bunchedBimonoidDeltaMulRightNe (coeffAt contractionIndex) contractionIndex targetIndex
                    (Nat.ne_of_lt (targetEqDim.symm ▸ indexBelow))))]
            exact bunchedBimonoidNatListSumMapZero (List.range dimension)
          rw [bunchedBimonoidDeltaMulRightEq (coeffAt dimension) dimension targetIndex targetEqDim.symm,
            headZero, targetEqDim]
          exact Nat.zero_add (coeffAt dimension)

/-- ★★ **THE LEFT DELTA COLLAPSE** `natListSum ((range n).map (fun k => (if i == k then 1 else 0) * coeffAt k))
= coeffAt i` for `i < n` — the mirror, the delta on the left factor.  Propext-clean. -/
theorem bunchedBimonoidDeltaCollapseLeft (coeffAt : Nat → Nat) : ∀ (dimension rowIndex : Nat),
    rowIndex < dimension →
    bunchedBimonoidNatListSum ((List.range dimension).map (fun contractionIndex =>
        (if rowIndex == contractionIndex then 1 else 0) * coeffAt contractionIndex))
      = coeffAt rowIndex
  | 0, _, below => absurd below (Nat.not_lt_zero _)
  | dimension + 1, rowIndex, rowBelow => by
      rw [bunchedBimonoidSumRangeSucc
        (fun contractionIndex => (if rowIndex == contractionIndex then 1 else 0) * coeffAt contractionIndex)
        dimension]
      match Nat.lt_or_ge rowIndex dimension with
      | Or.inl rowLtDim =>
          rw [bunchedBimonoidDeltaCollapseLeft coeffAt dimension rowIndex rowLtDim,
            bunchedBimonoidDeltaMulLeftNe (coeffAt dimension) rowIndex dimension (Nat.ne_of_lt rowLtDim)]
          rfl
      | Or.inr rowGeDim =>
          have rowEqDim : rowIndex = dimension :=
            Nat.le_antisymm (Nat.le_of_lt_succ rowBelow) rowGeDim
          have headZero : bunchedBimonoidNatListSum ((List.range dimension).map (fun contractionIndex =>
              (if rowIndex == contractionIndex then 1 else 0) * coeffAt contractionIndex)) = 0 := by
            rw [congrArg bunchedBimonoidNatListSum
              (bunchedBimonoidRangeMapCongr
                (fun contractionIndex =>
                  (if rowIndex == contractionIndex then 1 else 0) * coeffAt contractionIndex)
                (fun _ => 0) dimension
                (fun contractionIndex indexBelow =>
                  bunchedBimonoidDeltaMulLeftNe (coeffAt contractionIndex) rowIndex contractionIndex
                    (rowEqDim ▸ (Nat.ne_of_lt indexBelow).symm)))]
            exact bunchedBimonoidNatListSumMapZero (List.range dimension)
          rw [bunchedBimonoidDeltaMulLeftEq (coeffAt dimension) rowIndex dimension rowEqDim,
            headZero, rowEqDim]
          exact Nat.zero_add (coeffAt dimension)

/-- ★★★ **NODE A residual (2) — the general-`n` RIGHT identity unit** `matMul M (identityMat M.cols) = M` for
well-formed `M`.  Each `(i,j)` entry sums `matEntryAt M i k * delta(k, j)` over `k`, collapsing to `matEntryAt M i
j` (right delta collapse); the whole entries list rebuilds via `matReconstruct`.  Needs `wf` for reconstruction;
the delta collapse is `wf`-free. -/
theorem bunchedBimonoidIdentityRightUnit (matM : BunchedBimonoidMat)
    (wf : bunchedBimonoidMatWellFormed matM) :
    bunchedBimonoidMatMul matM (bunchedBimonoidIdentityMat matM.cols) = matM := by
  have entriesEq :
      (bunchedBimonoidMatMul matM (bunchedBimonoidIdentityMat matM.cols)).entries = matM.entries := by
    show (List.range matM.rows).map (fun rowIndex => (List.range matM.cols).map (fun colIndex =>
        bunchedBimonoidNatListSum ((List.range matM.cols).map (fun contractionIndex =>
          bunchedBimonoidMatEntryAt matM rowIndex contractionIndex
            * bunchedBimonoidMatEntryAt (bunchedBimonoidIdentityMat matM.cols) contractionIndex colIndex))))
      = matM.entries
    rw [bunchedBimonoidRangeMapCongr _
        (fun rowIndex => (List.range matM.cols).map (fun colIndex =>
          bunchedBimonoidMatEntryAt matM rowIndex colIndex)) matM.rows
        (fun rowIndex _ => bunchedBimonoidRangeMapCongr _
          (fun colIndex => bunchedBimonoidMatEntryAt matM rowIndex colIndex) matM.cols
          (fun colIndex colBelow => by
            rw [congrArg bunchedBimonoidNatListSum
              (bunchedBimonoidRangeMapCongr
                (fun contractionIndex => bunchedBimonoidMatEntryAt matM rowIndex contractionIndex
                  * bunchedBimonoidMatEntryAt (bunchedBimonoidIdentityMat matM.cols) contractionIndex colIndex)
                (fun contractionIndex => bunchedBimonoidMatEntryAt matM rowIndex contractionIndex
                  * (if contractionIndex == colIndex then 1 else 0)) matM.cols
                (fun contractionIndex indexBelow =>
                  congrArg (bunchedBimonoidMatEntryAt matM rowIndex contractionIndex * ·)
                    (bunchedBimonoidIdentityMatEntry matM.cols contractionIndex colIndex indexBelow colBelow)))]
            exact bunchedBimonoidDeltaCollapseRight (fun contractionIndex =>
              bunchedBimonoidMatEntryAt matM rowIndex contractionIndex) matM.cols colIndex colBelow))]
    exact bunchedBimonoidMatReconstruct matM wf
  calc bunchedBimonoidMatMul matM (bunchedBimonoidIdentityMat matM.cols)
      = BunchedBimonoidMat.mk matM.rows matM.cols
          (bunchedBimonoidMatMul matM (bunchedBimonoidIdentityMat matM.cols)).entries := rfl
    _ = BunchedBimonoidMat.mk matM.rows matM.cols matM.entries := by rw [entriesEq]
    _ = matM := rfl

/-- ★★★ **NODE A residual (2) — the general-`n` LEFT identity unit** `matMul (identityMat M.rows) M = M` for
well-formed `M`.  The mirror: each entry collapses via the left delta collapse (`delta(i, k) * matEntryAt M k j`),
then reconstruction. -/
theorem bunchedBimonoidIdentityLeftUnit (matM : BunchedBimonoidMat)
    (wf : bunchedBimonoidMatWellFormed matM) :
    bunchedBimonoidMatMul (bunchedBimonoidIdentityMat matM.rows) matM = matM := by
  have entriesEq :
      (bunchedBimonoidMatMul (bunchedBimonoidIdentityMat matM.rows) matM).entries = matM.entries := by
    show (List.range matM.rows).map (fun rowIndex => (List.range matM.cols).map (fun colIndex =>
        bunchedBimonoidNatListSum ((List.range matM.rows).map (fun contractionIndex =>
          bunchedBimonoidMatEntryAt (bunchedBimonoidIdentityMat matM.rows) rowIndex contractionIndex
            * bunchedBimonoidMatEntryAt matM contractionIndex colIndex))))
      = matM.entries
    rw [bunchedBimonoidRangeMapCongr _
        (fun rowIndex => (List.range matM.cols).map (fun colIndex =>
          bunchedBimonoidMatEntryAt matM rowIndex colIndex)) matM.rows
        (fun rowIndex rowBelow => bunchedBimonoidRangeMapCongr _
          (fun colIndex => bunchedBimonoidMatEntryAt matM rowIndex colIndex) matM.cols
          (fun colIndex _ => by
            rw [congrArg bunchedBimonoidNatListSum
              (bunchedBimonoidRangeMapCongr
                (fun contractionIndex =>
                  bunchedBimonoidMatEntryAt (bunchedBimonoidIdentityMat matM.rows) rowIndex contractionIndex
                    * bunchedBimonoidMatEntryAt matM contractionIndex colIndex)
                (fun contractionIndex => (if rowIndex == contractionIndex then 1 else 0)
                  * bunchedBimonoidMatEntryAt matM contractionIndex colIndex) matM.rows
                (fun contractionIndex indexBelow =>
                  congrArg (· * bunchedBimonoidMatEntryAt matM contractionIndex colIndex)
                    (bunchedBimonoidIdentityMatEntry matM.rows rowIndex contractionIndex rowBelow indexBelow)))]
            exact bunchedBimonoidDeltaCollapseLeft (fun contractionIndex =>
              bunchedBimonoidMatEntryAt matM contractionIndex colIndex) matM.rows rowIndex rowBelow))]
    exact bunchedBimonoidMatReconstruct matM wf
  calc bunchedBimonoidMatMul (bunchedBimonoidIdentityMat matM.rows) matM
      = BunchedBimonoidMat.mk matM.rows matM.cols
          (bunchedBimonoidMatMul (bunchedBimonoidIdentityMat matM.rows) matM).entries := rfl
    _ = BunchedBimonoidMat.mk matM.rows matM.cols matM.entries := by rw [entriesEq]
    _ = matM := rfl

/-- Truth-probe: the right unit specialises to a concrete `2 x 3` matrix on the nose (via the proved general
lemma; wf discharges by `rfl`). -/
theorem bunchedBimonoidIdentityRightUnitProbe :
    bunchedBimonoidMatMul { rows := 2, cols := 3, entries := [[1, 2, 3], [4, 5, 6]] }
        (bunchedBimonoidIdentityMat 3)
      = { rows := 2, cols := 3, entries := [[1, 2, 3], [4, 5, 6]] } :=
  bunchedBimonoidIdentityRightUnit { rows := 2, cols := 3, entries := [[1, 2, 3], [4, 5, 6]] }
    ⟨rfl, fun rowIndex rowBelow => match rowIndex, rowBelow with
              | 0, _ => rfl
              | 1, _ => rfl
              | _ + 2, below =>
                  absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ below)) (Nat.not_lt_zero _)⟩

/-! ## The B1 kit honesty marker (reconstruction + Fubini kit) -/

/-- ★★ **ESTABLISHED (B1 kit) — the reconstruction + Fubini kit is shipped, propext-clean.**  `= true` records
the genuinely-new content: the range-succ-CONS front primitive; the list-rebuild inductions
(`bunchedBimonoid{NatList,RowList}Rebuild`) and the matrix reconstruction (`bunchedBimonoidMatReconstruct`,
Node A residual (2)'s named target); the get-of-range-map readers; the matMul entry read; and the finite-sum
Fubini kit (`bunchedBimonoidAddMul` / `...MulAdd` / `...MulAssoc` hand-rolled, `...SumMul{Right,Left}`,
`...SumMapAdd`, and the double-induction `...NatListSumSwap`).  All STRUCTURAL, no `WellFounded.fix`, no Init
`add_mul` / `range_succ` / `getD`. -/
def fxBunchedBimonoid_reconstructionAndFubiniKitShipped : Bool := true

/-- ★★★ **ESTABLISHED (Node A residual 1) — general `matMul` associativity is SHIPPED.**  `= true` records
`bunchedBimonoidMatMulAssoc` (`matMul (matMul A B) C = matMul A (matMul B C)` for composable matrices) at full
generality — the r4 ledger's `fxBunchedBimonoid_r4RemainingNodeMatMulAssoc = false` is retired NAME-ONLY here
(that r4 marker keeps its name and value byte-intact; this fresh marker records the literal general delivery, no
longer only the r2 concrete `rfl` probes). -/
def fxBunchedBimonoid_nodeAMatMulAssocShipped : Bool := true

/-- ★★★ **ESTABLISHED (Node A residual 2) — the general-`n` identity unit laws are SHIPPED.**  `= true` records
`bunchedBimonoidIdentity{Right,Left}Unit` (`matMul M (identityMat M.cols) = M` and the left unit) for an ARBITRARY
well-formed `M`, via the matrix reconstruction the block-exchange deliberately dodged + the delta collapse.  The
r4 ledger's `fxBunchedBimonoid_r4RemainingNodeGeneralUnits = false` is retired NAME-ONLY (byte-intact); this fresh
marker records the literal general delivery, no longer only the `1 x 1` singletons. -/
def fxBunchedBimonoid_nodeAIdentityUnitsShipped : Bool := true

/-- ★★★ **THE BI DIVIDEND ADJUDICATION — Node A is COMPLETE; the strict-law matrix-soundness gate advances.**
`= true` records that BOTH Node A residuals of the r4 `matrixStrictLawExtensionReached` demand are now literally
met at full generality: (1) `bunchedBimonoidMatMulAssoc` (general associativity, the vcomp-interchange law's
matrix side) AND (2) `bunchedBimonoidIdentity{Right,Left}Unit` (general identity units, the `id`-cell law's matrix
side).  These are the two matrix laws the `StrictAxiomRel` half of the star scope needs.  Honest scope note: the
UPSTREAM marker `fxBunchedBimonoid_matrixStrictLawExtensionReached` (MatrixSemantics, r3) stays `= false`
byte-intact — its VERBATIM three-component demand also includes the block-multiplicativity of `directSum` under
the strict interchange, which the block-exchange shipped separately; this fresh marker adjudicates the two matMul
components (associativity + units) as MET, and does NOT flip the upstream `= false` (no fake flip; the upstream
marker's own text is the authority on its full scope). -/
def fxBunchedBimonoid_nodeAMatMulLawsCompleteBiDividend : Bool := true

end FX1Poly.Polygraph.Omega
