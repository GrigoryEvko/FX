import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidSpiderNormalForm

/-! # Polygraph/Omega/WalkingBunchedBimonoidSpiderRoundTrip — the general spider round-trip (WP-PROP r2, #2033)

★ **The GENERAL diagram-to-matrix round-trip, on the additive `Mat(N)` PROP.**  The r1 land
(`WalkingBunchedBimonoidSpiderNormalForm`) shipped the staged spider (`bunchedBimonoidDeltaFan`,
`bunchedBimonoidMuFold`, `bunchedBimonoidSpiderScalar`) with per-instance round-trips `evalCell (spider M) = M`
each closed by `rfl`, and NAMED three r2 walls for the general case:

  * `fxBunchedBimonoid_spiderGeneralStageLemmasReached = false` — "the general `evalCell deltaStage = C`,
    `evalCell muStage = Mg` ... need the same Fubini kit";
  * `fxBunchedBimonoid_spiderGeneralRoundTripReached = false` — "the universally-quantified round-trip needs the
    finite-sum Fubini / matMul-associativity kit (the same wall as `matrixStrictLawExtensionReached`)";
  * `fxBunchedBimonoid_spiderGeneralRoutingReached = false` — the row-major routing transpose.

This file BUILDS that shared kit and closes the general stage lemmas and the general scalar round-trip.  Every
r1 / r2 / r3 wall marker keeps its name and `= false` value byte-intact (this is the ADDITIVE advance; the
supersession is recorded name-only through fresh markers here).

## B1 — THE FUBINI KIT: the missing `Mat(N)` lemmas as structural inductions

The r1 matrix operations (`bunchedBimonoidMatMul`, `bunchedBimonoidMatDirectSum`, `bunchedBimonoidIdentityMat`)
are `List.range`-generated, so per-instance facts are `rfl`, but NO algebra lemma about them existed — the empty
Fubini kit the walls point at.  This brick ships it as propext-clean structural inductions: the `List.range`
reindexing kit (`...RangeSuccSnoc`, `...RangeMapConstIsReplicate` — Init's `List.range_succ` / `List.map_append`
/ `List.replicate_succ'` all leak `propext`, so every member is hand-rolled cons/`Nat`-structural), the
finite-sum append law (`...NatListSumAppend`), and the `getD`-at-range read kit
(`...{Nat,Row}ListGetReplicate{SnocLow,SnocHigh,Low}`) — the `List.getD`-free indexers stay propext-clean.
matMul associativity is truth-probed as a `rfl` theorem on concrete `2 x 2` and non-square blocks FIRST.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B1 — THE FUBINI KIT: the missing Mat(N) lemmas as structural inductions
    # =========================================================================================

★ **The truth-probe FIRST: matMul associativity holds `rfl` on concrete blocks.**  The `List.range`-generated
`bunchedBimonoidMatMul` has FIXED contraction ranges (the recon's zero-dim tax makes composability extrinsic), so
`(A . B) . C = A . (B . C)` is a definitional equality on closed inputs — machine-confirmed on a `2 x 2` and a
non-square chain before any general lemma. -/

/-! ## The truth-probe — matMul associativity on concrete blocks (`rfl`) -/

/-- ★ **TRUTH-PROBE (matMul associativity, `2 x 2`).**  `(A . B) . C = A . (B . C)` for concrete `2 x 2` blocks,
by `rfl` — the fixed contraction ranges make associativity definitional on closed inputs.  The first probe the
recon mandates before building the general kit. -/
theorem bunchedBimonoidMatMulAssocConcreteTwoByTwo :
    bunchedBimonoidMatMul
        (bunchedBimonoidMatMul { rows := 2, cols := 2, entries := [[1, 2], [3, 4]] }
          { rows := 2, cols := 2, entries := [[5, 6], [7, 8]] })
        { rows := 2, cols := 2, entries := [[1, 0], [1, 1]] }
      = bunchedBimonoidMatMul { rows := 2, cols := 2, entries := [[1, 2], [3, 4]] }
        (bunchedBimonoidMatMul { rows := 2, cols := 2, entries := [[5, 6], [7, 8]] }
          { rows := 2, cols := 2, entries := [[1, 0], [1, 1]] }) := rfl

/-- ★ **TRUTH-PROBE (matMul associativity, non-square `2x3 . 3x2 . 2x2`).**  Associativity holds `rfl` across a
non-square chain too — the contraction ranges track the shared inner dimensions with no dimension mismatch. -/
theorem bunchedBimonoidMatMulAssocConcreteNonSquare :
    bunchedBimonoidMatMul
        (bunchedBimonoidMatMul { rows := 2, cols := 3, entries := [[1, 2, 3], [4, 5, 6]] }
          { rows := 3, cols := 2, entries := [[1, 0], [0, 1], [1, 1]] })
        { rows := 2, cols := 2, entries := [[2, 0], [0, 3]] }
      = bunchedBimonoidMatMul { rows := 2, cols := 3, entries := [[1, 2, 3], [4, 5, 6]] }
        (bunchedBimonoidMatMul { rows := 3, cols := 2, entries := [[1, 0], [0, 1], [1, 1]] }
          { rows := 2, cols := 2, entries := [[2, 0], [0, 3]] }) := rfl

#eval bunchedBimonoidMatMul
  (bunchedBimonoidMatMul { rows := 2, cols := 2, entries := [[1, 2], [3, 4]] }
    { rows := 2, cols := 2, entries := [[5, 6], [7, 8]] })
  { rows := 2, cols := 2, entries := [[1, 0], [1, 1]] }

/-! ## The `List.range` reindexing kit — every member hand-rolled (Init's leaks `propext`) -/

/-- **List append associativity** — cons-structural, propext-clean (Init's `List.append_assoc` leaks `propext`
through the match-compiler).  The workhorse for the `List.range` accumulator factoring. -/
theorem bunchedBimonoidListAppendAssoc {carrier : Type} :
    ∀ (elements moreElements evenMoreElements : List carrier),
    (elements ++ moreElements) ++ evenMoreElements = elements ++ (moreElements ++ evenMoreElements)
  | [], _, _ => rfl
  | element :: elements, moreElements, evenMoreElements =>
      congrArg (element :: ·) (bunchedBimonoidListAppendAssoc elements moreElements evenMoreElements)

/-- **Map distributes over append** — cons-structural, propext-clean (Init's `List.map_append` leaks). -/
theorem bunchedBimonoidMapAppendDistrib {source target : Type} (transform : source → target) :
    ∀ (elements moreElements : List source),
    (elements ++ moreElements).map transform = elements.map transform ++ moreElements.map transform
  | [], _ => rfl
  | element :: elements, moreElements =>
      congrArg (transform element :: ·) (bunchedBimonoidMapAppendDistrib transform elements moreElements)

/-- **Map of a replicate is a replicate** — the linchpin for the block-diagonal fan / row matrices (each row of a
`List.replicate`-block maps to a constant row).  Structural on the count, propext-clean. -/
theorem bunchedBimonoidMapReplicate {source target : Type} (transform : source → target) (value : source) :
    ∀ (count : Nat), (List.replicate count value).map transform = List.replicate count (transform value)
  | 0 => rfl
  | count + 1 => congrArg (transform value :: ·) (bunchedBimonoidMapReplicate transform value count)

/-- **A replicate re-snoc** `replicate (count+1) v = replicate count v ++ [v]` — structural, propext-clean (Init's
`List.replicate_succ'` leaks).  Closes the successor step of the range-map-const lemma. -/
theorem bunchedBimonoidReplicateSuccSnoc {carrier : Type} (value : carrier) :
    ∀ (count : Nat), List.replicate (count + 1) value = List.replicate count value ++ [value]
  | 0 => rfl
  | count + 1 => congrArg (value :: ·) (bunchedBimonoidReplicateSuccSnoc value count)

/-- **The `List.range.loop` accumulator factors** `range.loop count acc = range.loop count [] ++ acc` — the clean
core of the range successor law (the loop prepends, so the accumulator distributes out on the right).  Structural
on the count; `range.loop (count+1) acc = range.loop count (count :: acc)` reduces by `rfl` (verified). -/
theorem bunchedBimonoidRangeLoopFactors : ∀ (count : Nat) (accumulated : List Nat),
    List.range.loop count accumulated = List.range.loop count [] ++ accumulated
  | 0, _ => rfl
  | count + 1, accumulated => by
      have loopHead : List.range.loop (count + 1) accumulated
          = List.range.loop count [] ++ (count :: accumulated) :=
        bunchedBimonoidRangeLoopFactors count (count :: accumulated)
      have loopEmpty : List.range.loop (count + 1) ([] : List Nat)
          = List.range.loop count [] ++ [count] :=
        bunchedBimonoidRangeLoopFactors count [count]
      rw [loopHead, loopEmpty]
      exact (bunchedBimonoidListAppendAssoc (List.range.loop count []) [count] accumulated).symm

/-- ★ **The range successor snoc** `List.range (count+1) = List.range count ++ [count]` — hand-rolled from the
accumulator factoring (Init's `List.range_succ` leaks `propext`).  The reindexing backbone for reasoning about
the `List.range`-generated matMul rows. -/
theorem bunchedBimonoidRangeSuccSnoc (count : Nat) :
    List.range (count + 1) = List.range count ++ [count] :=
  bunchedBimonoidRangeLoopFactors count [count]

/-- ★ **The range-map-const collapses to a replicate** — if `transform` is constant `value` on `[0, count)` then
`(List.range count).map transform = List.replicate count value`.  THE Fubini linchpin: a matMul row whose every
contraction lands the same value collapses to an all-`value` column.  Structural on the count via the range
successor snoc + map-append + replicate snoc — all hand-rolled, propext-clean. -/
theorem bunchedBimonoidRangeMapConstIsReplicate {carrier : Type} (transform : Nat → carrier) (value : carrier) :
    ∀ (count : Nat), (∀ index, index < count → transform index = value) →
      (List.range count).map transform = List.replicate count value
  | 0, _ => rfl
  | count + 1, constantOnRange => by
      rw [bunchedBimonoidRangeSuccSnoc, bunchedBimonoidMapAppendDistrib]
      rw [bunchedBimonoidRangeMapConstIsReplicate transform value count
        (fun index below => constantOnRange index (Nat.lt_succ_of_lt below))]
      rw [List.map_cons, List.map_nil, constantOnRange count (Nat.lt_succ_self count)]
      exact (bunchedBimonoidReplicateSuccSnoc value count).symm

/-! ## The finite-sum append law -/

/-- ★ **The contraction sum is additive over append** `natListSum (xs ++ ys) = natListSum xs + natListSum ys` —
the finite-sum Fubini half (a split contraction range sums block-wise).  Structural on the first list; the
successor step closes by `Nat.add_assoc` alone (propext-clean — `add_assoc` / `add_comm` are clean, `add_mul`
leaks). -/
theorem bunchedBimonoidNatListSumAppend : ∀ (elements moreElements : List Nat),
    bunchedBimonoidNatListSum (elements ++ moreElements)
      = bunchedBimonoidNatListSum elements + bunchedBimonoidNatListSum moreElements
  | [], moreElements => (Nat.zero_add _).symm
  | element :: elements, moreElements => by
      show element + bunchedBimonoidNatListSum (elements ++ moreElements)
        = (element + bunchedBimonoidNatListSum elements) + bunchedBimonoidNatListSum moreElements
      rw [bunchedBimonoidNatListSumAppend elements moreElements, Nat.add_assoc]

/-! ## The getD-at-range read kit — split reads on a `replicate ++ [tail]` block -/

/-- **Low read of a snoc'd replicate** `natListGet (replicate count v ++ [w]) index = v` for `index < count` —
the interior of a fanned block reads the replicated cell.  Structural on the count and index; propext-clean. -/
theorem bunchedBimonoidNatListGetReplicateSnocLow (value tailValue : Nat) : ∀ (count index : Nat), index < count →
    bunchedBimonoidNatListGet (List.replicate count value ++ [tailValue]) index = value
  | 0, _, below => absurd below (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | count + 1, index + 1, below =>
      bunchedBimonoidNatListGetReplicateSnocLow value tailValue count index (Nat.lt_of_succ_lt_succ below)

/-- **High read of a snoc'd replicate** `natListGet (replicate count v ++ [w]) count = w` — the boundary cell (the
identity block's own entry) reads the snoc'd tail.  Structural, propext-clean. -/
theorem bunchedBimonoidNatListGetReplicateSnocHigh (value tailValue : Nat) : ∀ (count : Nat),
    bunchedBimonoidNatListGet (List.replicate count value ++ [tailValue]) count = tailValue
  | 0 => rfl
  | count + 1 => bunchedBimonoidNatListGetReplicateSnocHigh value tailValue count

/-- **Low row-read of a snoc'd replicate** `rowListGet (replicate count r ++ [s]) index = r` for `index < count` —
the row-level analogue for block matrices whose top-left is a replicated row.  Structural, propext-clean. -/
theorem bunchedBimonoidRowListGetReplicateSnocLow (row tailRow : List Nat) : ∀ (count index : Nat), index < count →
    bunchedBimonoidRowListGet (List.replicate count row ++ [tailRow]) index = row
  | 0, _, below => absurd below (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | count + 1, index + 1, below =>
      bunchedBimonoidRowListGetReplicateSnocLow row tailRow count index (Nat.lt_of_succ_lt_succ below)

/-- **High row-read of a snoc'd replicate** `rowListGet (replicate count r ++ [s]) count = s` — the boundary row.
Structural, propext-clean. -/
theorem bunchedBimonoidRowListGetReplicateSnocHigh (row tailRow : List Nat) : ∀ (count : Nat),
    bunchedBimonoidRowListGet (List.replicate count row ++ [tailRow]) count = tailRow
  | 0 => rfl
  | count + 1 => bunchedBimonoidRowListGetReplicateSnocHigh row tailRow count

/-- **Interior read of a bare replicate** `natListGet (replicate count v) index = v` for `index < count` — the
row-of-ones read for the scalar round-trip's contraction.  Structural, propext-clean. -/
theorem bunchedBimonoidNatListGetReplicateLow (value : Nat) : ∀ (count index : Nat), index < count →
    bunchedBimonoidNatListGet (List.replicate count value) index = value
  | 0, _, below => absurd below (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | count + 1, index + 1, below =>
      bunchedBimonoidNatListGetReplicateLow value count index (Nat.lt_of_succ_lt_succ below)

/-- **Interior row-read of a bare replicate** `rowListGet (replicate count r) index = r` for `index < count`.
Structural, propext-clean. -/
theorem bunchedBimonoidRowListGetReplicateLow (row : List Nat) : ∀ (count index : Nat), index < count →
    bunchedBimonoidRowListGet (List.replicate count row) index = row
  | 0, _, below => absurd below (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | count + 1, index + 1, below =>
      bunchedBimonoidRowListGetReplicateLow row count index (Nat.lt_of_succ_lt_succ below)

/-- **Sum of an all-ones replicate is the count** `natListSum (replicate count 1) = count` — the multiplicity
scalar `[[n]]` arises as this sum over the `n` merged wires.  Structural; the step closes by `Nat.add_comm`
(clean). -/
theorem bunchedBimonoidNatListSumReplicateOne : ∀ (count : Nat),
    bunchedBimonoidNatListSum (List.replicate count 1) = count
  | 0 => rfl
  | count + 1 => by
      show 1 + bunchedBimonoidNatListSum (List.replicate count 1) = count + 1
      rw [bunchedBimonoidNatListSumReplicateOne count, Nat.add_comm]

/-! ## The B1 honesty marker -/

/-- ★★ **ESTABLISHED (B1) — the matMul-algebra Fubini kit is shipped, propext-clean.**  `= true` records the
missing `Mat(N)` lemmas as structural inductions: matMul associativity truth-probed `rfl` on concrete `2 x 2` /
non-square blocks (`bunchedBimonoidMatMulAssocConcrete{TwoByTwo,NonSquare}`); the hand-rolled `List.range`
reindexing kit (`bunchedBimonoidRange{LoopFactors,SuccSnoc,MapConstIsReplicate}`, plus `...ListAppendAssoc`,
`...MapAppendDistrib`, `...MapReplicate`, `...ReplicateSuccSnoc` — Init's `range_succ` / `map_append` /
`replicate_succ'` all leak `propext`, so each is re-derived cons/`Nat`-structural); the finite-sum append law
(`...NatListSumAppend`); and the `getD`-at-range read kit (`...{Nat,Row}ListGetReplicate{SnocLow,SnocHigh,Low}`,
`...NatListSumReplicateOne`).  This is the kit the r2 `fxBunchedBimonoid_spiderGeneralStageLemmasReached` /
`...spiderGeneralRoundTripReached` and the r3 `fxBunchedBimonoid_matrixStrictLawExtensionReached` walls point at;
those wall markers keep their name and `= false` value byte-intact (this is the additive advance). -/
def fxBunchedBimonoid_matMulFubiniKitShipped : Bool := true

/-! # =========================================================================================
    # B2 — THE GENERAL STAGE LEMMAS: deltaFan -> fanMatrix, muFold -> rowMatrix, spiderScalar -> [[n]]
    # =========================================================================================

★ **The three r2-walled general stage lemmas, closed for ALL `n` by induction matching the word's own
recursion.**  The delta-stage building block `bunchedBimonoidDeltaFan n` evaluates to the `n x 1` all-ones copy
column `bunchedBimonoidFanMatrix n`; the mu-stage `bunchedBimonoidMuFold n` to the `1 x n` all-ones fold row
`bunchedBimonoidRowMatrix n`; and the scalar spider `bunchedBimonoidSpiderScalar n` to the `1 x 1` multiplicity
matrix `[[n]]` — the general round-trip for the whole `1 x 1` / column / row family, not merely the r1
per-instance `rfl` probes.  The inductive step at `k+2` reduces `evalCell` DEFINITIONALLY to a
`matMul (directSum ... (identityMat 1)) ...`, then the B1 Fubini kit (`...RangeMapConstIsReplicate` +
`getD`-at-range reads) collapses the row-major matMul to the all-ones replicate.  Every intermediate matrix stays
in `List.range` / `List.replicate` normal form — the recon's escape hatch that AVOIDS general matrix
extensionality. -/

/-! ## The stage target matrices -/

/-- ★ The **fan matrix** `bunchedBimonoidFanMatrix n` — the `n x 1` all-ones copy column (`n` outputs, one
input).  The delta-stage's `Mat(N)` value. -/
def bunchedBimonoidFanMatrix (dimension : Nat) : BunchedBimonoidMat :=
  { rows := dimension, cols := 1, entries := List.replicate dimension [1] }

/-- ★ The **row matrix** `bunchedBimonoidRowMatrix n` — the `1 x n` all-ones fold row (one output, `n` inputs).
The mu-stage's `Mat(N)` value. -/
def bunchedBimonoidRowMatrix (dimension : Nat) : BunchedBimonoidMat :=
  { rows := 1, cols := dimension, entries := [List.replicate dimension 1] }

/-- The fan matrix at `2` agrees with the shipped `evalCell (deltaFan 2)` (base-case pin, `rfl`). -/
theorem bunchedBimonoidFanMatrixMatchesDeltaFanTwo :
    bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan 2) = bunchedBimonoidFanMatrix 2 := rfl

/-- The row matrix at `2` agrees with the shipped `evalCell (muFold 2)` (base-case pin, `rfl`). -/
theorem bunchedBimonoidRowMatrixMatchesMuFoldTwo :
    bunchedBimonoidEvalCell (bunchedBimonoidMuFold 2) = bunchedBimonoidRowMatrix 2 := rfl

/-! ## The delta-stage block reads (the `directSum (fanMatrix (k+1)) (identityMat 1)` entries) -/

/-- The fan block `directSum (fanMatrix (k+1)) (identityMat 1)` has `entries` a `[1,0]`-replicate snoc'd with the
identity row `[0,1]` — `mapReplicate` collapses the top-left block; the bottom identity row is `rfl`. -/
theorem bunchedBimonoidFanBlockEntries (rank : Nat) :
    (bunchedBimonoidMatDirectSum (bunchedBimonoidFanMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1)).entries
      = List.replicate (rank + 1) [1, 0] ++ [[0, 1]] :=
  congrArg (· ++ [[0, 1]]) (bunchedBimonoidMapReplicate (fun row => row ++ List.replicate 1 0) [1] (rank + 1))

/-- Interior fan-block entry, column 0 — reads `1` (the copy strand) for a row `< rank+1`. -/
theorem bunchedBimonoidFanBlockEntryLowZero (rank index : Nat) (below : index < rank + 1) :
    bunchedBimonoidMatEntryAt
        (bunchedBimonoidMatDirectSum (bunchedBimonoidFanMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1))
        index 0 = 1 := by
  show bunchedBimonoidNatListGet (bunchedBimonoidRowListGet
    (bunchedBimonoidMatDirectSum (bunchedBimonoidFanMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1)).entries
      index) 0 = 1
  rw [bunchedBimonoidFanBlockEntries, bunchedBimonoidRowListGetReplicateSnocLow [1, 0] [0, 1] (rank + 1) index below]
  rfl

/-- Interior fan-block entry, column 1 — reads `0` (the off-diagonal) for a row `< rank+1`. -/
theorem bunchedBimonoidFanBlockEntryLowOne (rank index : Nat) (below : index < rank + 1) :
    bunchedBimonoidMatEntryAt
        (bunchedBimonoidMatDirectSum (bunchedBimonoidFanMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1))
        index 1 = 0 := by
  show bunchedBimonoidNatListGet (bunchedBimonoidRowListGet
    (bunchedBimonoidMatDirectSum (bunchedBimonoidFanMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1)).entries
      index) 1 = 0
  rw [bunchedBimonoidFanBlockEntries, bunchedBimonoidRowListGetReplicateSnocLow [1, 0] [0, 1] (rank + 1) index below]
  rfl

/-- Boundary fan-block entry (the identity row), column 0 — reads `0`. -/
theorem bunchedBimonoidFanBlockEntryHighZero (rank : Nat) :
    bunchedBimonoidMatEntryAt
        (bunchedBimonoidMatDirectSum (bunchedBimonoidFanMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1))
        (rank + 1) 0 = 0 := by
  show bunchedBimonoidNatListGet (bunchedBimonoidRowListGet
    (bunchedBimonoidMatDirectSum (bunchedBimonoidFanMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1)).entries
      (rank + 1)) 0 = 0
  rw [bunchedBimonoidFanBlockEntries, bunchedBimonoidRowListGetReplicateSnocHigh [1, 0] [0, 1] (rank + 1)]
  rfl

/-- Boundary fan-block entry (the identity row), column 1 — reads `1`. -/
theorem bunchedBimonoidFanBlockEntryHighOne (rank : Nat) :
    bunchedBimonoidMatEntryAt
        (bunchedBimonoidMatDirectSum (bunchedBimonoidFanMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1))
        (rank + 1) 1 = 1 := by
  show bunchedBimonoidNatListGet (bunchedBimonoidRowListGet
    (bunchedBimonoidMatDirectSum (bunchedBimonoidFanMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1)).entries
      (rank + 1)) 1 = 1
  rw [bunchedBimonoidFanBlockEntries, bunchedBimonoidRowListGetReplicateSnocHigh [1, 0] [0, 1] (rank + 1)]
  rfl

/-- ★ Every row of `matMul (fanBlock (k+1)) delta` is the singleton `[1]` — the fan block contracted against the
`delta` copy matrix `[[1],[1]]` sums each row (either `[1,0]` or `[0,1]`) to `1`.  Case-split on interior vs
boundary row; the B1 block reads finish it. -/
theorem bunchedBimonoidFanMatMulRowIsOne (rank index : Nat) (below : index < rank + 2) :
    (List.range 1).map (fun colIndex =>
      bunchedBimonoidNatListSum ((List.range 2).map (fun contractionIndex =>
        bunchedBimonoidMatEntryAt
            (bunchedBimonoidMatDirectSum (bunchedBimonoidFanMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1))
            index contractionIndex
          * bunchedBimonoidMatEntryAt { rows := 2, cols := 1, entries := [[1], [1]] } contractionIndex colIndex)))
      = [1] := by
  match Nat.lt_or_ge index (rank + 1) with
  | Or.inl interior =>
      show [bunchedBimonoidMatEntryAt _ index 0 * 1 + (bunchedBimonoidMatEntryAt _ index 1 * 1 + 0)] = [1]
      rw [bunchedBimonoidFanBlockEntryLowZero rank index interior,
        bunchedBimonoidFanBlockEntryLowOne rank index interior]
  | Or.inr boundary =>
      have atBoundary : index = rank + 1 := Nat.le_antisymm (Nat.le_of_lt_succ below) boundary
      subst atBoundary
      show [bunchedBimonoidMatEntryAt _ (rank + 1) 0 * 1 + (bunchedBimonoidMatEntryAt _ (rank + 1) 1 * 1 + 0)] = [1]
      rw [bunchedBimonoidFanBlockEntryHighZero rank, bunchedBimonoidFanBlockEntryHighOne rank]

/-- ★★ **STAGE LEMMA (delta) — `evalCell (deltaFan n) = fanMatrix n` for ALL `n`.**  The general delta-stage
evaluation the r2 `fxBunchedBimonoid_spiderGeneralStageLemmasReached` walled: the fan of `n` copies evaluates to
the `n x 1` all-ones column.  Structural recursion matching `deltaFan`'s `0 / 1 / k+2` split; the `k+2` step
reduces `evalCell` definitionally to `matMul (directSum (fanMatrix (k+1)) (identityMat 1)) delta`, and
`bunchedBimonoidRangeMapConstIsReplicate` (via `bunchedBimonoidFanMatMulRowIsOne`) collapses it to
`fanMatrix (k+2)`. -/
theorem bunchedBimonoidDeltaFanMatrix : ∀ (dimension : Nat),
    bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan dimension) = bunchedBimonoidFanMatrix dimension
  | 0 => rfl
  | 1 => rfl
  | rank + 2 => by
      have inductionHypothesis :
          bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan (rank + 1)) = bunchedBimonoidFanMatrix (rank + 1) :=
        bunchedBimonoidDeltaFanMatrix (rank + 1)
      show bunchedBimonoidMatMul
        (bunchedBimonoidMatDirectSum (bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan (rank + 1)))
          (bunchedBimonoidIdentityMat 1))
        { rows := 2, cols := 1, entries := [[1], [1]] } = bunchedBimonoidFanMatrix (rank + 2)
      rw [inductionHypothesis]
      have entriesEq :
          (List.range (rank + 2)).map (fun rowIndex =>
            (List.range 1).map (fun colIndex =>
              bunchedBimonoidNatListSum ((List.range 2).map (fun contractionIndex =>
                bunchedBimonoidMatEntryAt
                    (bunchedBimonoidMatDirectSum (bunchedBimonoidFanMatrix (rank + 1))
                      (bunchedBimonoidIdentityMat 1)) rowIndex contractionIndex
                  * bunchedBimonoidMatEntryAt { rows := 2, cols := 1, entries := [[1], [1]] } contractionIndex colIndex))))
            = List.replicate (rank + 2) [1] :=
        bunchedBimonoidRangeMapConstIsReplicate _ [1] (rank + 2)
          (fun index below => bunchedBimonoidFanMatMulRowIsOne rank index below)
      exact congrArg
        (fun matrixEntries => ({ rows := rank + 2, cols := 1, entries := matrixEntries } : BunchedBimonoidMat))
        entriesEq

/-! ## The mu-stage block reads (the `directSum (rowMatrix (k+1)) (identityMat 1)` entries) -/

/-- Mu-block first row (the fold row), interior column — reads `1`. -/
theorem bunchedBimonoidRowBlockEntryFirstLow (rank index : Nat) (below : index < rank + 1) :
    bunchedBimonoidMatEntryAt
        (bunchedBimonoidMatDirectSum (bunchedBimonoidRowMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1))
        0 index = 1 := by
  show bunchedBimonoidNatListGet (List.replicate (rank + 1) 1 ++ [0]) index = 1
  exact bunchedBimonoidNatListGetReplicateSnocLow 1 0 (rank + 1) index below

/-- Mu-block first row, boundary column — reads `0`. -/
theorem bunchedBimonoidRowBlockEntryFirstHigh (rank : Nat) :
    bunchedBimonoidMatEntryAt
        (bunchedBimonoidMatDirectSum (bunchedBimonoidRowMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1))
        0 (rank + 1) = 0 := by
  show bunchedBimonoidNatListGet (List.replicate (rank + 1) 1 ++ [0]) (rank + 1) = 0
  exact bunchedBimonoidNatListGetReplicateSnocHigh 1 0 (rank + 1)

/-- Mu-block second row (the identity row), interior column — reads `0`. -/
theorem bunchedBimonoidRowBlockEntrySecondLow (rank index : Nat) (below : index < rank + 1) :
    bunchedBimonoidMatEntryAt
        (bunchedBimonoidMatDirectSum (bunchedBimonoidRowMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1))
        1 index = 0 := by
  show bunchedBimonoidNatListGet (List.replicate (rank + 1) 0 ++ [1]) index = 0
  exact bunchedBimonoidNatListGetReplicateSnocLow 0 1 (rank + 1) index below

/-- Mu-block second row, boundary column — reads `1`. -/
theorem bunchedBimonoidRowBlockEntrySecondHigh (rank : Nat) :
    bunchedBimonoidMatEntryAt
        (bunchedBimonoidMatDirectSum (bunchedBimonoidRowMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1))
        1 (rank + 1) = 1 := by
  show bunchedBimonoidNatListGet (List.replicate (rank + 1) 0 ++ [1]) (rank + 1) = 1
  exact bunchedBimonoidNatListGetReplicateSnocHigh 0 1 (rank + 1)

/-- ★ Every column of `matMul mu (rowBlock (k+1))` is `1` — the `mu` fold row `[[1,1]]` contracted against the
mu-block sums each column (either the fold row or the identity row) to `1`.  Case-split on interior vs boundary
column. -/
theorem bunchedBimonoidRowMatMulColIsOne (rank index : Nat) (below : index < rank + 2) :
    bunchedBimonoidNatListSum ((List.range 2).map (fun contractionIndex =>
      bunchedBimonoidMatEntryAt { rows := 1, cols := 2, entries := [[1, 1]] } 0 contractionIndex
        * bunchedBimonoidMatEntryAt
            (bunchedBimonoidMatDirectSum (bunchedBimonoidRowMatrix (rank + 1)) (bunchedBimonoidIdentityMat 1))
            contractionIndex index)) = 1 := by
  match Nat.lt_or_ge index (rank + 1) with
  | Or.inl interior =>
      show 1 * bunchedBimonoidMatEntryAt _ 0 index + (1 * bunchedBimonoidMatEntryAt _ 1 index + 0) = 1
      rw [bunchedBimonoidRowBlockEntryFirstLow rank index interior,
        bunchedBimonoidRowBlockEntrySecondLow rank index interior]
  | Or.inr boundary =>
      have atBoundary : index = rank + 1 := Nat.le_antisymm (Nat.le_of_lt_succ below) boundary
      subst atBoundary
      show 1 * bunchedBimonoidMatEntryAt _ 0 (rank + 1) + (1 * bunchedBimonoidMatEntryAt _ 1 (rank + 1) + 0) = 1
      rw [bunchedBimonoidRowBlockEntryFirstHigh rank, bunchedBimonoidRowBlockEntrySecondHigh rank]

/-- ★★ **STAGE LEMMA (mu) — `evalCell (muFold n) = rowMatrix n` for ALL `n`.**  The dual of the delta stage: the
fold of `n` wires evaluates to the `1 x n` all-ones row.  Structural recursion matching `muFold`'s `0 / 1 / k+2`
split; the `k+2` step reduces to `matMul mu (directSum (rowMatrix (k+1)) (identityMat 1))`, and the Fubini kit
collapses the single row to `rowMatrix (k+2)`. -/
theorem bunchedBimonoidMuFoldMatrix : ∀ (dimension : Nat),
    bunchedBimonoidEvalCell (bunchedBimonoidMuFold dimension) = bunchedBimonoidRowMatrix dimension
  | 0 => rfl
  | 1 => rfl
  | rank + 2 => by
      have inductionHypothesis :
          bunchedBimonoidEvalCell (bunchedBimonoidMuFold (rank + 1)) = bunchedBimonoidRowMatrix (rank + 1) :=
        bunchedBimonoidMuFoldMatrix (rank + 1)
      show bunchedBimonoidMatMul { rows := 1, cols := 2, entries := [[1, 1]] }
        (bunchedBimonoidMatDirectSum (bunchedBimonoidEvalCell (bunchedBimonoidMuFold (rank + 1)))
          (bunchedBimonoidIdentityMat 1)) = bunchedBimonoidRowMatrix (rank + 2)
      rw [inductionHypothesis]
      have entriesEq :
          (List.range 1).map (fun _rowIndex =>
            (List.range (rank + 2)).map (fun colIndex =>
              bunchedBimonoidNatListSum ((List.range 2).map (fun contractionIndex =>
                bunchedBimonoidMatEntryAt { rows := 1, cols := 2, entries := [[1, 1]] } 0 contractionIndex
                  * bunchedBimonoidMatEntryAt
                      (bunchedBimonoidMatDirectSum (bunchedBimonoidRowMatrix (rank + 1))
                        (bunchedBimonoidIdentityMat 1)) contractionIndex colIndex))))
            = [List.replicate (rank + 2) 1] := by
        show [(List.range (rank + 2)).map _] = [List.replicate (rank + 2) 1]
        exact congrArg (fun singleRow => [singleRow])
          (bunchedBimonoidRangeMapConstIsReplicate _ 1 (rank + 2)
            (fun index below => bunchedBimonoidRowMatMulColIsOne rank index below))
      exact congrArg
        (fun matrixEntries => ({ rows := 1, cols := rank + 2, entries := matrixEntries } : BunchedBimonoidMat))
        entriesEq

/-! ## The general scalar round-trip — `evalCell (spiderScalar n) = [[n]]` for ALL `n` -/

/-- The scalar contraction product `rowMatrix n` against `fanMatrix n` is `1` at each of the `n` shared wires. -/
theorem bunchedBimonoidScalarProductIsOne (dimension contractionIndex : Nat) (below : contractionIndex < dimension) :
    bunchedBimonoidMatEntryAt (bunchedBimonoidRowMatrix dimension) 0 contractionIndex
      * bunchedBimonoidMatEntryAt (bunchedBimonoidFanMatrix dimension) contractionIndex 0 = 1 := by
  have rowRead : bunchedBimonoidMatEntryAt (bunchedBimonoidRowMatrix dimension) 0 contractionIndex = 1 := by
    show bunchedBimonoidNatListGet (List.replicate dimension 1) contractionIndex = 1
    exact bunchedBimonoidNatListGetReplicateLow 1 dimension contractionIndex below
  have fanRead : bunchedBimonoidMatEntryAt (bunchedBimonoidFanMatrix dimension) contractionIndex 0 = 1 := by
    show bunchedBimonoidNatListGet
      (bunchedBimonoidRowListGet (List.replicate dimension [1]) contractionIndex) 0 = 1
    rw [bunchedBimonoidRowListGetReplicateLow [1] dimension contractionIndex below]
    rfl
  rw [rowRead, fanRead]

/-- ★★ **GENERAL SCALAR ROUND-TRIP — `evalCell (spiderScalar n) = [[n]]` for ALL `n`.**  The general `1 x 1`
round-trip the r2 `fxBunchedBimonoid_spiderGeneralRoundTripReached` walled for the scalar family: the multiplicity
spider (fan into `n` wires, merge `n` wires) evaluates to `[[n]]` on the nose.  From the two stage lemmas
(`spiderScalar n = vcomp (deltaFan n) (muFold n)` evaluates to `matMul (rowMatrix n) (fanMatrix n)`), the Fubini
kit contracts the `n` shared wires to `natListSum (replicate n 1) = n`.  This lifts the r1 per-instance `rfl`
probes (`[[0]] / [[1]] / [[2]] / [[3]]`) to the universally-quantified theorem. -/
theorem bunchedBimonoidSpiderScalarMatrix (dimension : Nat) :
    bunchedBimonoidEvalCell (bunchedBimonoidSpiderScalar dimension)
      = { rows := 1, cols := 1, entries := [[dimension]] } := by
  show bunchedBimonoidMatMul (bunchedBimonoidEvalCell (bunchedBimonoidMuFold dimension))
    (bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan dimension))
      = { rows := 1, cols := 1, entries := [[dimension]] }
  rw [bunchedBimonoidMuFoldMatrix, bunchedBimonoidDeltaFanMatrix]
  have contractionEq :
      (List.range dimension).map (fun contractionIndex =>
        bunchedBimonoidMatEntryAt (bunchedBimonoidRowMatrix dimension) 0 contractionIndex
          * bunchedBimonoidMatEntryAt (bunchedBimonoidFanMatrix dimension) contractionIndex 0)
        = List.replicate dimension 1 :=
    bunchedBimonoidRangeMapConstIsReplicate _ 1 dimension
      (fun contractionIndex below => bunchedBimonoidScalarProductIsOne dimension contractionIndex below)
  have sumEq :
      bunchedBimonoidNatListSum ((List.range dimension).map (fun contractionIndex =>
        bunchedBimonoidMatEntryAt (bunchedBimonoidRowMatrix dimension) 0 contractionIndex
          * bunchedBimonoidMatEntryAt (bunchedBimonoidFanMatrix dimension) contractionIndex 0)) = dimension := by
    rw [contractionEq, bunchedBimonoidNatListSumReplicateOne]
  exact congrArg
    (fun scalar => ({ rows := 1, cols := 1, entries := [[scalar]] } : BunchedBimonoidMat)) sumEq

/-! ## B2 truth-probe outputs (the general lemmas instantiated at n = 0,1,2,3) -/

#eval bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan 3)   -- fanMatrix 3
#eval bunchedBimonoidEvalCell (bunchedBimonoidMuFold 3)     -- rowMatrix 3
#eval bunchedBimonoidEvalCell (bunchedBimonoidSpiderScalar 4)  -- [[4]]

/-! ## The B2 honesty markers -/

/-- ★★ **ESTABLISHED (B2) — the general stage lemmas are shipped for ALL `n`.**  `= true` records the three
universally-quantified stage evaluations: `bunchedBimonoidDeltaFanMatrix` (`evalCell (deltaFan n) = fanMatrix n`,
the `n x 1` copy column), `bunchedBimonoidMuFoldMatrix` (`evalCell (muFold n) = rowMatrix n`, the `1 x n` fold
row), and `bunchedBimonoidSpiderScalarMatrix` (`evalCell (spiderScalar n) = [[n]]`, the general scalar
round-trip).  Each is a structural induction matching the word's own `0 / 1 / k+2` recursion, closed by the B1
Fubini kit with every intermediate matrix in `List.range` / `List.replicate` normal form (no general matrix
extensionality).  The r2 wall `fxBunchedBimonoid_spiderGeneralStageLemmasReached = false` — verbatim "the general
`evalCell deltaStage = C`, `evalCell muStage = Mg` ... need the same Fubini kit" — keeps its name and `= false`
value byte-intact; this fresh marker records the additive delivery. -/
def fxBunchedBimonoid_spiderStageLemmasGeneralShipped : Bool := true

/-- ★★ **ESTABLISHED (B2) — the general scalar round-trip is shipped for ALL `n`.**  `= true` records
`bunchedBimonoidSpiderScalarMatrix`: `evalCell (spiderScalar n) = [[n]]` universally, lifting the r1 per-instance
`rfl` probes (`[[0]] / [[1]] / [[2]] / [[3]]`) to the `forall n` theorem.  This is the general round-trip for the
`1 x 1` (scalar / multiplicity) sub-family — the first universally-quantified fragment of the r2 wall
`fxBunchedBimonoid_spiderGeneralRoundTripReached = false` (verbatim "the universally-quantified round-trip needs
the finite-sum Fubini / matMul-associativity kit"), whose name and `= false` value stay byte-intact.  The FULL
matrix round-trip (arbitrary `q x p` via the column-peel constructor) is B3. -/
def fxBunchedBimonoid_spiderScalarRoundTripGeneralShipped : Bool := true

end FX1Poly.Polygraph.Omega
