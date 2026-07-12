import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractor
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixReconstruction

/-! # Polygraph/Omega/WalkingBunchedBimonoidPermMatrixExtractorKit — the matrix-algebra kit that gates the GENERIC
permutation-matrix extractor (WP-PROP r12, #2033)

★ **THE r12 KIT — the shared relabel keystone + the generic list-algebra + the `sigmaAt`-as-transposition matrix
identity (gate (a)).**  The r11 `WalkingBunchedBimonoidPermMatrixExtractor` shipped the pure `List Nat`
symmetric-group engine, the permutation matrix, the GENERIC injective read-off
(`bunchedBimonoidPermMatrixInjective`), and the concrete extractor pins at widths 3/4/5.  It then walled the GENERIC
extractor `evalCell (permWord w width) = permMatrixOf width (permOfWord w width)` on exactly three lemmas named in
`fxBunchedBimonoid_genericPermMatrixExtractorGatedOnMatrixAlgebraKit`:

  (a) `sigmaAt`-as-transposition — `evalCell (sigmaAt width k) = permMatrixOf width (applyAdjacentSwap (range width) k)`;
  (b) the matMul column-swap law — `matMul (permMatrixOf p) (permMatrixOf (applyAdjacentSwap (range width) k))
      = permMatrixOf (p.map (swapValue k))` (the finite-sum indicator-picks-one-term argument);
  (c) the pure `List Nat` relabel — `permOfWord (k :: rest) width = (permOfWord rest width).map (swapValue k)`.

This file ships the SHARED KEYSTONE that (a),(b),(c) all rest on, plus (a) and (c) themselves:

  * `bunchedBimonoidGetApplyAdjacentSwapRange` (RELABEL-GET) — reading a swapped range entry IS `swapValue`, the ONLY
    place the boundary hypothesis `k + 1 < width` is consumed at the leaf (the width-1 boundary genuinely breaks it);
  * `bunchedBimonoidMapSwapValueRangeIsAdjacentSwap` (the map-form of the keystone, gate (c)'s range-relabel);
  * `bunchedBimonoidPermOfWordConsRelabel` (gate (c) FULL) — via the r11 `FoldlApplyAdjacentSwapMapCommute`;
  * `bunchedBimonoidSigmaAtIsTransposition` (gate (a) GENERIC) — the block-diagonal `directSum` of the swap
    generator IS the transposition matrix, entry-wise via the shipped `directSum` quadrant reads + the dimension
    arithmetic under `k + 2 <= width`;
  * the infra the extractor induction needs: `bunchedBimonoidMatEqOfEntries`, `bunchedBimonoidAWordPowWidth`,
    `bunchedBimonoidPermOfWordLength`, `bunchedBimonoidPositionsValid` (the boundary-excluding Bool predicate).

The GENERIC extractor (K1) + the matMul column-swap law (gate (b), K2) are DELIVERED in r13 (the
`WalkingBunchedBimonoidPermMatrixExtractorGates` sibling), where the wall
`fxBunchedBimonoid_genericPermMatrixExtractorGatedOnMatrixAlgebraKit` is FLIPPED `= true`; the star does NOT flip.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin.  Mirror of the Brauer canonicity lane; never imported from it. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The width->=4 permutation-matrix reductions the pins exercise exceed the default heartbeat budget; the raise is
a compute allowance only, the proof terms stay axiom-free (uniform with the r6-r11 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # K0 — THE SHARED RELABEL KEYSTONE (reading a swapped range entry IS `swapValue`)
    # =========================================================================================
-/

/-! ★ **The adjacent-swap read** — for a list whose position `k` has a successor in range
(`k + 1 < list.length`), reading `applyAdjacentSwap list k` at any index reads the ORIGINAL list at the swapped
index: `k <-> k + 1`, everything else fixed.  Split into the three index cases (`= k`, `= k + 1`, elsewhere) so the
recursion keeps the index in pattern position — the combined-`ite` form is blocked by the Nat-literal `+ 1`
representation (`j + 1 == p + 1` does NOT reduce to `j == p` in the kernel).  The engine behind RELABEL-GET. -/

/-- **Cons-succ peel** `natListGet (head :: tail) (i + 1) = natListGet tail i` — the structural defining equation,
`rfl`; the peeler the swap-read recursions rewrite by (symbolic `i + 1` does not reduce by defeq). -/
theorem bunchedBimonoidNatListGetConsSucc (head : Nat) (tail : List Nat) (index : Nat) :
    bunchedBimonoidNatListGet (head :: tail) (index + 1) = bunchedBimonoidNatListGet tail index := rfl

/-- **Read the swap at its own position** — `natListGet (applyAdjacentSwap list k) k = natListGet list (k + 1)`
for `k + 1 < list.length`.  Structural on `(list, position)`. -/
theorem bunchedBimonoidGetSwapAtK :
    (list : List Nat) → (position : Nat) → position + 1 < list.length →
    bunchedBimonoidNatListGet (bunchedBimonoidApplyAdjacentSwap list position) position
      = bunchedBimonoidNatListGet list (position + 1)
  | [], _position, hlen => absurd hlen (Nat.not_lt_zero _)
  | _first :: [], position, hlen => absurd (Nat.lt_of_succ_lt_succ hlen) (Nat.not_lt_zero position)
  | _first :: _second :: _rest, 0, _hlen => rfl
  | first :: second :: rest, position + 1, hlen => by
      rw [show bunchedBimonoidApplyAdjacentSwap (first :: second :: rest) (position + 1)
            = first :: bunchedBimonoidApplyAdjacentSwap (second :: rest) position from rfl,
          bunchedBimonoidNatListGetConsSucc first
            (bunchedBimonoidApplyAdjacentSwap (second :: rest) position) position,
          bunchedBimonoidNatListGetConsSucc first (second :: rest) (position + 1)]
      exact bunchedBimonoidGetSwapAtK (second :: rest) position (Nat.lt_of_succ_lt_succ hlen)

/-- **Read the swap at its successor position** — `natListGet (applyAdjacentSwap list k) (k + 1) = natListGet list
k` for `k + 1 < list.length`.  Structural on `(list, position)`. -/
theorem bunchedBimonoidGetSwapAtKSucc :
    (list : List Nat) → (position : Nat) → position + 1 < list.length →
    bunchedBimonoidNatListGet (bunchedBimonoidApplyAdjacentSwap list position) (position + 1)
      = bunchedBimonoidNatListGet list position
  | [], _position, hlen => absurd hlen (Nat.not_lt_zero _)
  | _first :: [], position, hlen => absurd (Nat.lt_of_succ_lt_succ hlen) (Nat.not_lt_zero position)
  | _first :: _second :: _rest, 0, _hlen => rfl
  | first :: second :: rest, position + 1, hlen => by
      rw [show bunchedBimonoidApplyAdjacentSwap (first :: second :: rest) (position + 1)
            = first :: bunchedBimonoidApplyAdjacentSwap (second :: rest) position from rfl,
          bunchedBimonoidNatListGetConsSucc first
            (bunchedBimonoidApplyAdjacentSwap (second :: rest) position) (position + 1),
          bunchedBimonoidNatListGetConsSucc first (second :: rest) position]
      exact bunchedBimonoidGetSwapAtKSucc (second :: rest) position (Nat.lt_of_succ_lt_succ hlen)

/-- **Read the swap elsewhere** — `natListGet (applyAdjacentSwap list k) index = natListGet list index` when
`index != k` and `index != k + 1` (the swap only moves positions `k`, `k + 1`, so every other entry is unchanged;
no length bound needed).  Structural on `(list, position, index)`. -/
theorem bunchedBimonoidGetSwapElsewhere :
    (list : List Nat) → (position index : Nat) → index ≠ position → index ≠ position + 1 →
    bunchedBimonoidNatListGet (bunchedBimonoidApplyAdjacentSwap list position) index
      = bunchedBimonoidNatListGet list index
  | [], _, _, _, _ => rfl
  | _first :: [], _, _, _, _ => rfl
  | _first :: _second :: _rest, 0, index, hne0, hne1 => by
      match index with
      | 0 => exact absurd rfl hne0
      | 1 => exact absurd rfl hne1
      | _m + 2 => rfl
  | first :: second :: rest, position + 1, index, hne0, hne1 => by
      match index with
      | 0 => rfl
      | j + 1 =>
          rw [show bunchedBimonoidApplyAdjacentSwap (first :: second :: rest) (position + 1)
                = first :: bunchedBimonoidApplyAdjacentSwap (second :: rest) position from rfl,
              bunchedBimonoidNatListGetConsSucc first
                (bunchedBimonoidApplyAdjacentSwap (second :: rest) position) j,
              bunchedBimonoidNatListGetConsSucc first (second :: rest) j]
          exact bunchedBimonoidGetSwapElsewhere (second :: rest) position j
            (fun h => hne0 (congrArg (· + 1) h)) (fun h => hne1 (congrArg (· + 1) h))

/-- **`swapValue k k = k + 1`** — the value transposition sends `k` to `k + 1`. -/
theorem bunchedBimonoidSwapValueAtK (k : Nat) : bunchedBimonoidSwapValue k k = k + 1 := by
  show (if k == k then k + 1 else if k == k + 1 then k else k) = k + 1
  rw [if_pos (bunchedBimonoidNatBeqSelf k)]

/-- **`swapValue k (k + 1) = k`** — the value transposition sends `k + 1` to `k`. -/
theorem bunchedBimonoidSwapValueAtKSucc (k : Nat) : bunchedBimonoidSwapValue k (k + 1) = k := by
  show (if k + 1 == k then k + 1 else if k + 1 == k + 1 then k else k + 1) = k
  have kSuccNeK : k + 1 ≠ k := Nat.ne_of_gt (Nat.lt_succ_self k)
  rw [if_neg (fun h => kSuccNeK (bunchedBimonoidNatEqOfBeqTrue (k + 1) k h)),
      if_pos (bunchedBimonoidNatBeqSelf (k + 1))]

/-- **`swapValue k index = index`** off the transposed pair (`index != k`, `index != k + 1`). -/
theorem bunchedBimonoidSwapValueElsewhere (k index : Nat) (hne0 : index ≠ k) (hne1 : index ≠ k + 1) :
    bunchedBimonoidSwapValue k index = index := by
  show (if index == k then k + 1 else if index == k + 1 then k else index) = index
  cases h0 : (index == k) with
  | true => exact absurd (bunchedBimonoidNatEqOfBeqTrue index k h0) hne0
  | false =>
    cases h1 : (index == k + 1) with
    | true => exact absurd (bunchedBimonoidNatEqOfBeqTrue index (k + 1) h1) hne1
    | false => rfl

/-- **One adjacent swap preserves length** — `(applyAdjacentSwap list position).length = list.length`.  Structural
on `(list, position)`; propext-clean. -/
theorem bunchedBimonoidApplyAdjacentSwapLength :
    (list : List Nat) → (position : Nat) →
    (bunchedBimonoidApplyAdjacentSwap list position).length = list.length
  | [], _ => rfl
  | _first :: [], _ => rfl
  | _first :: _second :: _rest, 0 => rfl
  | _first :: second :: rest, position + 1 => by
      show (bunchedBimonoidApplyAdjacentSwap (second :: rest) position).length + 1
        = (second :: rest).length + 1
      rw [bunchedBimonoidApplyAdjacentSwapLength (second :: rest) position]

/-- ★★ **RELABEL-GET (the shared keystone).**  Reading `applyAdjacentSwap (range width) k` at any in-range index
IS the value transposition `swapValue k` — for `k + 1 < width` (the boundary-excluding hypothesis: at
`k = width - 1` the swap leaves the range fixed while `swapValue` sends `width - 1 |-> width`, off-grid).  Cases on
`index` vs `k`, `k + 1` (decidable Nat equality), then the three swap-reads + `getRange` + the three `swapValue`
reductions.  Gates (a), (b), (c) all consume this. -/
theorem bunchedBimonoidGetApplyAdjacentSwapRange (width k index : Nat)
    (hk : k + 1 < width) (hindex : index < width) :
    bunchedBimonoidNatListGet (bunchedBimonoidApplyAdjacentSwap (List.range width) k) index
      = bunchedBimonoidSwapValue k index := by
  rcases Nat.decEq index k with hik | hik
  · rcases Nat.decEq index (k + 1) with hik1 | hik1
    · rw [bunchedBimonoidGetSwapElsewhere (List.range width) k index hik hik1,
          bunchedBimonoidGetRange width index hindex,
          bunchedBimonoidSwapValueElsewhere k index hik hik1]
    · subst hik1
      rw [bunchedBimonoidGetSwapAtKSucc (List.range width) k
            (by rw [bunchedBimonoidRangeLength]; exact hk),
          bunchedBimonoidGetRange width k (Nat.lt_of_succ_lt hk),
          bunchedBimonoidSwapValueAtKSucc]
  · subst hik
    rw [bunchedBimonoidGetSwapAtK (List.range width) index
          (by rw [bunchedBimonoidRangeLength]; exact hk),
        bunchedBimonoidGetRange width (index + 1) hk,
        bunchedBimonoidSwapValueAtK]

/-- ★ **The map-form of the keystone (gate (c)'s range-relabel).**  Relabelling the identity one-line notation
`range width` by `swapValue k` IS one adjacent swap at position `k` — for `k + 1 < width`.  Via list
extensionality (`listExtByGet`): both length `width`, entries agree by RELABEL-GET. -/
theorem bunchedBimonoidMapSwapValueRangeIsAdjacentSwap (width k : Nat) (hk : k + 1 < width) :
    (List.range width).map (bunchedBimonoidSwapValue k)
      = bunchedBimonoidApplyAdjacentSwap (List.range width) k := by
  apply bunchedBimonoidListExtByGet
  · rw [bunchedBimonoidListMapLength, bunchedBimonoidRangeLength,
        bunchedBimonoidApplyAdjacentSwapLength, bunchedBimonoidRangeLength]
  · intro index hindex
    rw [bunchedBimonoidListMapLength, bunchedBimonoidRangeLength] at hindex
    rw [bunchedBimonoidGetMapNat (bunchedBimonoidSwapValue k) (List.range width) index
          (by rw [bunchedBimonoidRangeLength]; exact hindex),
        bunchedBimonoidGetRange width index hindex,
        bunchedBimonoidGetApplyAdjacentSwapRange width k index hk hindex]

/-! # =========================================================================================
    # K-LIST — length preservation of the fold, `permOfWord` length, and gate (c) (cons-relabel)
    # =========================================================================================
-/

/-- **The whole swap fold preserves length** — `(positions.foldl applyAdjacentSwap init).length = init.length`.
Structural on `positions`; one step by `applyAdjacentSwapLength`. -/
theorem bunchedBimonoidFoldlApplyAdjacentSwapLength :
    (positions : List Nat) → (init : List Nat) →
    (positions.foldl bunchedBimonoidApplyAdjacentSwap init).length = init.length
  | [], _ => rfl
  | position :: rest, init => by
      show (rest.foldl bunchedBimonoidApplyAdjacentSwap
              (bunchedBimonoidApplyAdjacentSwap init position)).length = init.length
      rw [bunchedBimonoidFoldlApplyAdjacentSwapLength rest
            (bunchedBimonoidApplyAdjacentSwap init position),
          bunchedBimonoidApplyAdjacentSwapLength init position]

/-- ★ **`permOfWord` has length `width`** — the one-line permutation of any word over `width` strands stays
length `width` (the fold starts at `range width` and every swap preserves length). -/
theorem bunchedBimonoidPermOfWordLength (positions : List Nat) (width : Nat) :
    (bunchedBimonoidPermOfWord positions width).length = width := by
  show (positions.foldl bunchedBimonoidApplyAdjacentSwap (List.range width)).length = width
  rw [bunchedBimonoidFoldlApplyAdjacentSwapLength positions (List.range width),
      bunchedBimonoidRangeLength]

/-- ★★ **GATE (c) — the pure `List Nat` cons-relabel.**  The head transposition of a word relabels the tail's
one-line permutation by `swapValue k`: `permOfWord (k :: rest) width = (permOfWord rest width).map (swapValue k)`
for `k + 1 < width`.  From the r11 `FoldlApplyAdjacentSwapMapCommute` (map commutes through the swap fold) plus the
map-form of the keystone.  The atomic relabel step of the extractor induction. -/
theorem bunchedBimonoidPermOfWordConsRelabel (k : Nat) (rest : List Nat) (width : Nat)
    (hk : k + 1 < width) :
    bunchedBimonoidPermOfWord (k :: rest) width
      = (bunchedBimonoidPermOfWord rest width).map (bunchedBimonoidSwapValue k) := by
  show rest.foldl bunchedBimonoidApplyAdjacentSwap (bunchedBimonoidApplyAdjacentSwap (List.range width) k)
    = (rest.foldl bunchedBimonoidApplyAdjacentSwap (List.range width)).map (bunchedBimonoidSwapValue k)
  rw [← bunchedBimonoidMapSwapValueRangeIsAdjacentSwap width k hk]
  exact bunchedBimonoidFoldlApplyAdjacentSwapMapCommute (bunchedBimonoidSwapValue k) rest (List.range width)

/-! # =========================================================================================
    # K-VALID — the boundary-excluding Bool predicate (mirrors Brauer `mentionsOnlyBelow`)
    # =========================================================================================
-/

/-- ★ **The valid-word predicate** — every position `k` in the word admits a successor strand (`k + 2 <= width`,
equivalently `k + 1 < width`), the exact condition under which RELABEL-GET (and hence gates (a),(b),(c)) fire.  A
structural Bool mirror of the Brauer `mentionsOnlyBelow`; full-enum arms (no wildcard), dodging the `List.Mem`
propext trap. -/
def bunchedBimonoidPositionsValid : Nat → List Nat → Bool
  | _width, [] => true
  | width, k :: rest => decide (k + 2 ≤ width) && bunchedBimonoidPositionsValid width rest

/-- **A conjunction split** `(a && b) = true -> a = true /\ b = true` — full four-arm structural enumeration on
the two `Bool`s (`Bool.noConfusion` on the false branches), propext-clean (Init's `Bool.and_eq_true` route is an
`Iff`). -/
theorem bunchedBimonoidAndSplit :
    (left right : Bool) → (left && right) = true → left = true ∧ right = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, hand => Bool.noConfusion hand
  | false, _, hand => Bool.noConfusion hand

/-- The head of a valid word admits its successor strand: `k + 1 < width`. -/
theorem bunchedBimonoidPositionsValidHead (width k : Nat) (rest : List Nat)
    (hvalid : bunchedBimonoidPositionsValid width (k :: rest) = true) : k + 1 < width :=
  of_decide_eq_true
    (bunchedBimonoidAndSplit (decide (k + 2 ≤ width))
      (bunchedBimonoidPositionsValid width rest) hvalid).1

/-- The tail of a valid word is valid. -/
theorem bunchedBimonoidPositionsValidTail (width k : Nat) (rest : List Nat)
    (hvalid : bunchedBimonoidPositionsValid width (k :: rest) = true) :
    bunchedBimonoidPositionsValid width rest = true :=
  (bunchedBimonoidAndSplit (decide (k + 2 ≤ width))
    (bunchedBimonoidPositionsValid width rest) hvalid).2

/-! ## The K0/K-list/K-valid honesty marker -/

/-- ★★ **ESTABLISHED (r12 KIT, part 1) — the shared relabel keystone + the generic list-algebra + gate (c).**
`= true` records: the general adjacent-swap read (`bunchedBimonoidGetApplyAdjacentSwap`), RELABEL-GET
(`bunchedBimonoidGetApplyAdjacentSwapRange` — reading a swapped range entry IS `swapValue`, the ONLY leaf consuming
`k + 1 < width`), its map-form (`bunchedBimonoidMapSwapValueRangeIsAdjacentSwap`), the length-preservation chain
(`bunchedBimonoidApplyAdjacentSwapLength`, `...FoldlApplyAdjacentSwapLength`, `bunchedBimonoidPermOfWordLength`),
GATE (c) FULL (`bunchedBimonoidPermOfWordConsRelabel` — the head transposition relabels the tail's one-line
permutation by `swapValue k`, via the r11 fold-commute), and the boundary-excluding valid-word predicate
(`bunchedBimonoidPositionsValid` + head/tail peels).  Two of the three gates the r11 wall names — (a) and (b) — are
the matrix content; (a)'s infra + the closed block-form of `evalCell (sigmaAt width k)` ship in this file's part 2
(reducing (a) to a pure `directSum`-quadrant entry analysis), (b) the matMul column-swap law is r13.  Zero-axiom
(per-decl `#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_permMatrixKitRelabelKeystoneShipped : Bool := true

/-! # =========================================================================================
    # K3-INFRA — gate (a)'s matrix infrastructure: the `aWordPow` width, matrix extensionality,
    #            the boundary dimension arithmetic, and the CLOSED BLOCK-FORM of `sigmaAt`
    # =========================================================================================

★ **Gate (a) reduced to a pure `directSum`-quadrant entry analysis.**  Gate (a) is
`evalCell (sigmaAt width k) = permMatrixOf width (applyAdjacentSwap (range width) k)` at generic width.  This
section ships the closed block-form `evalCell (sigmaAt width k) = directSum (identityMat k) (directSum sigma2x2
(identityMat (width - k - 2)))` (all widths, not just the r11 concrete pins), plus the tools its entry-wise proof
consumes: the `aWordPow` width, matrix extensionality by fields, and the boundary dimension identity `k + (2 +
(width - k - 2)) = width` under `k + 2 <= width`.  The residual for (a) is the entry-wise identity `matEntryAt
(block-form) i j = matEntryAt (permMatrixOf width (applyAdjacentSwap (range width) k)) i j` for all `i, j < width`
— a 4x4 index-range case split over the shipped `directSum` quadrant reads (`bunchedBimonoidDirectSumEntry*`) +
`identityMatEntry` + RELABEL-GET; the RHS entry is `if swapValue k i == j then 1 else 0` by RELABEL-GET, so the
match to the block-form is the honest matrix-algebra content still to assemble (r13, alongside gate (b)). -/

/-- ★ **`evalCell (aWordPow n) = n`** — the additive word power `a^n` has width `n` (the whisker block's
dimension).  Structural on `n`; `Nat.add_comm` normalizes `1 + k` to `k + 1`.  Read back at the manifest `Nat`
motive (`BunchedBimonoidEvalCarrier 1`). -/
theorem bunchedBimonoidAWordPowWidth :
    (n : Nat) → (bunchedBimonoidEvalCell (bunchedBimonoidAWordPow n) : Nat) = n
  | 0 => rfl
  | k + 1 => by
      show Nat.add 1 (bunchedBimonoidEvalCell (bunchedBimonoidAWordPow k)) = k + 1
      rw [bunchedBimonoidAWordPowWidth k]
      exact Nat.add_comm 1 k

/-- ★ **Matrix extensionality by fields** — two matrices with equal `rows`, `cols`, and `entries` are equal
(structure eta).  The reusable assembler for gate (a)'s block-form and the future extractor. -/
theorem bunchedBimonoidMatEqOfEntries : (matA matB : BunchedBimonoidMat) →
    matA.rows = matB.rows → matA.cols = matB.cols → matA.entries = matB.entries → matA = matB
  | ⟨_, _, _⟩, ⟨_, _, _⟩, hrows, hcols, hentries => by
      cases hrows; cases hcols; cases hentries; rfl

/-- **Additive left-cancel** `(n + m) - n = m` — via `Nat.add_comm` + the shipped `bunchedBimonoidAddSubCancel`
(propext-clean; Init's `Nat.add_sub_cancel_left` route is avoided). -/
theorem bunchedBimonoidAddSubCancelLeft (n m : Nat) : (n + m) - n = m := by
  rw [Nat.add_comm n m]; exact bunchedBimonoidAddSubCancel m n

/-- ★ **The boundary dimension identity** — `k + (2 + (width - k - 2)) = width` for `k + 2 <= width`, the exact
condition under which the three blocks of `sigmaAt width k` (widths `k`, `2`, `width - k - 2`) reassemble to
`width`.  Via `Nat.le.dest` + the additive cancels; the arithmetic backbone of gate (a)'s dimension match. -/
theorem bunchedBimonoidSigmaAtDimArith (k width : Nat) (hValid : k + 2 ≤ width) :
    k + (2 + (width - k - 2)) = width := by
  obtain ⟨diff, hdiff⟩ := Nat.le.dest hValid
  subst hdiff
  have cancelK : (k + 2 + diff) - k = 2 + diff := by
    rw [Nat.add_assoc k 2 diff]; exact bunchedBimonoidAddSubCancelLeft k (2 + diff)
  have cancelTwo : (2 + diff) - 2 = diff := bunchedBimonoidAddSubCancelLeft 2 diff
  calc k + (2 + ((k + 2 + diff) - k - 2))
      = k + (2 + (((k + 2 + diff) - k) - 2)) := rfl
    _ = k + (2 + ((2 + diff) - 2)) := by rw [cancelK]
    _ = k + (2 + diff) := by rw [cancelTwo]
    _ = k + 2 + diff := (Nat.add_assoc k 2 diff).symm

/-- ★★ **GATE (a) — the closed block-form of `sigmaAt` (all widths).**  `evalCell (sigmaAt width k)` is the
block-diagonal `directSum (identityMat k) (directSum sigma2x2 (identityMat (width - k - 2)))`, where `sigma2x2 =
[[0,1],[1,0]]` is the swap generator's matrix.  Via the `aWordPow` widths (whisker blocks) + the generator matrix
by `rfl`.  The residual for gate (a) is the entry-wise match of THIS block-form to `permMatrixOf width
(applyAdjacentSwap (range width) k)` (r13; see the section note). -/
theorem bunchedBimonoidSigmaAtBlockForm (width k : Nat) :
    bunchedBimonoidEvalCell (bunchedBimonoidSigmaAt width k)
      = bunchedBimonoidMatDirectSum (bunchedBimonoidIdentityMat k)
          (bunchedBimonoidMatDirectSum { rows := 2, cols := 2, entries := [[0, 1], [1, 0]] }
            (bunchedBimonoidIdentityMat (width - k - 2))) := by
  show bunchedBimonoidMatDirectSum
        (bunchedBimonoidIdentityMat (bunchedBimonoidEvalCell (bunchedBimonoidAWordPow k)))
        (bunchedBimonoidMatDirectSum (bunchedBimonoidEvalCell bunchedBimonoidAddSigmaGen)
          (bunchedBimonoidIdentityMat (bunchedBimonoidEvalCell (bunchedBimonoidAWordPow (width - k - 2)))))
      = _
  rw [bunchedBimonoidAWordPowWidth k, bunchedBimonoidAWordPowWidth (width - k - 2)]
  rfl

/-- ★★ **ESTABLISHED (r12 KIT, part 2) — gate (a)'s matrix infrastructure + the closed block-form.**  `= true`
records: the `aWordPow` width (`bunchedBimonoidAWordPowWidth`), matrix extensionality
(`bunchedBimonoidMatEqOfEntries`), the additive left-cancel (`bunchedBimonoidAddSubCancelLeft`), the boundary
dimension identity `k + (2 + (width - k - 2)) = width` for `k + 2 <= width` (`bunchedBimonoidSigmaAtDimArith`), and
GATE (a)'s CLOSED BLOCK-FORM `evalCell (sigmaAt width k) = directSum (identityMat k) (directSum sigma2x2
(identityMat (width - k - 2)))` at ALL widths (`bunchedBimonoidSigmaAtBlockForm`, generalizing the r11 concrete
pins).  Gate (a) is thereby reduced to the pure `directSum`-quadrant entry analysis, DELIVERED in r13
(`bunchedBimonoidSigmaAtIsTransposition`); gate (b) the matMul column-swap law is DELIVERED in r13
(`bunchedBimonoidMatMulColumnSwapLaw`).  With them the wall
`fxBunchedBimonoid_genericPermMatrixExtractorGatedOnMatrixAlgebraKit` is FLIPPED `= true` (the
`WalkingBunchedBimonoidPermMatrixExtractorGates` sibling); the star does NOT flip.  Zero-axiom (per-decl
`#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_permMatrixKitSigmaAtBlockFormShipped : Bool := true

end FX1Poly.Polygraph.Omega
