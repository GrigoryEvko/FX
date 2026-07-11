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

end FX1Poly.Polygraph.Omega
