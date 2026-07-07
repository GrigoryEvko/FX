import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellDriver

/-! # mode-3 keystone — Piece I: the redex-step disorder drop AT DEPTH + the `CellDescentResult` builders

`SpineValleyDisorder` proved the two strict-decrease facts for a redex at the HEAD of the tag word
(`countInversions_swap_adjacent_lt` for COMMUTE, `countInversions_delete_head_lt` for STRAIGHTEN), and its own
`swapFirstCupCap_disorder_lt` for the driver's recursive bubble.  But the cell oracle locates its redex, via
`readbackSplit_exposesRedex`, as an ARBITRARY-DEPTH split `capPrefix ++ cupAtom :: capAtom :: suffixRest`, and it
produces `next` by chain surgery at that split — so `next.spine` is the swapped / deleted word UNDER the same
`capPrefix`.  The oracle's `disorderDrops` field therefore needs the strict drop for a redex located behind an
arbitrary prefix, and — for COMMUTE — with the two moved atoms carrying re-threaded contexts (record updates that
preserve the cup/cap TAG but change the boundary paths).

This file ships that drop, purely at the disorder (inversion-count) layer, and the two builders that reduce the
oracle's per-step to its genuine residual (producing `next` with a `SaturatedTwoCellConv cell next`):

  * ★ **`countInversions_prefixSwap_lt` / `countInversions_prefixDelete_lt`** — the head strict-decrease facts
    lifted to an arbitrary prefix.  The append homomorphism (`countInversions_append`) factors off `capPrefix`;
    the within-suffix count strictly drops by the shipped head fact; the cross term is preserved by an adjacent
    swap (`crossInversionCount_swap_adjacent`) and only grows under a delete (`crossInversionCount_le_delete2`).
  * ★ **`crossInversionCount_swap_adjacent` / `crossInversionCount_le_delete2`** — the cross-term facts (swap
    invariance, delete monotonicity) the prefix drops rest on, from the shipped `countBelowThreshold_swap_adjacent`.
  * ★ **`countInversions_prefixCons2_slotCongr`** — the slot-congruence: two words that differ only by replacing
    the located pair with slot-equal atoms have the SAME inversion count.  This is what lets the COMMUTE drop see
    through the swap's context re-threading (the moved atoms keep their `isCupAtom` tag, hence their slot).
  * ★ **`spineDisorder_swap_lt` / `spineDisorder_delete_lt`** — the spine specializations on the cup/cap tag: a
    COMMUTE (swap the located cup·cap for a slot-preserving cap·cup) and a STRAIGHTEN (delete the located cup·cap)
    each strictly drop `spineDisorder`, at arbitrary depth.
  * ★ **`cellDescentResult_ofCommuteStep` / `cellDescentResult_ofStraightenStep`** — the two `CellDescentResult`
    builders.  Given a `next` cell, a `SaturatedTwoCellConv cell next`, and the source/target spine splits, each
    packages a `CellDescentResult cell`, discharging `disorderDrops` by the spine drop above.  So the oracle's
    per-step is reduced to exactly: EXHIBIT the located redex's move as `(next, stepConv)`.

## What this does NOT close (gates stay `false`)

The builders take `(next, stepConv)` as inputs.  Producing them for the located redex is the genuine open node:

  * COMMUTE — `next` is the chain-surgery reassembly with the two atoms transposed; the shipped
    `adjunctionSpineAtomSwap_of_disjointWindows` / `adjunctionSwappedPair_isBoundaryChained` realize the swap and
    its chain preservation only at the flat boundary-LENGTH level, whereas building `next`'s
    `RealizedSpineChain` (and its Godement `stepConv`) needs the swap at the boundary-PATH level (the re-threaded
    contexts shift the intermediate anchor path) — not yet lifted;
  * STRAIGHTEN — `stepConv` is `snakeStraightensInContext` fed a collapse witness `cupFrame ⊟ capFrame ≈ id`,
    which window-distance-1 alone does NOT supply (a shared-leg non-partner crossing neither collapses nor
    commutes); closing it needs the adjacent-redex-is-partner bridge (the arc non-crossing partner discipline
    lifted to the cell level) plus the deferred composite-1-cell whisker functoriality.

So `CellDescentStepOracle` stays UN-inhabited; `MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3 gate
flags stay `false`.  This file makes the disorder half of the oracle's per-step RIGOROUS and isolates the residual
to the `(next, stepConv)` production.

Raw Lean 4 + Init; the drops are `countInversions_append` + the shipped head facts + explicit `Nat` monotonicity
(no `omega`, no AC-`simp`); the builders are the spine drop threaded through the split equations.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## The cross-term facts: swap invariance and delete monotonicity -/

/-- The below-threshold count only grows when two elements are prepended: deleting an adjacent pair from a list
can only decrease the count below any threshold. -/
theorem countBelowThreshold_le_cons2 {α : Type u} (slotValue : α → Nat) (threshold : Nat)
    (firstCell secondCell : α) (rest : List α) :
    countBelowThreshold slotValue threshold rest
      ≤ countBelowThreshold slotValue threshold (firstCell :: secondCell :: rest) := by
  show countBelowThreshold slotValue threshold rest
    ≤ (if slotValue firstCell < threshold then 1 else 0)
        + ((if slotValue secondCell < threshold then 1 else 0)
            + countBelowThreshold slotValue threshold rest)
  exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_left _ _)

/-- **The cross-inversion count is invariant under an adjacent swap of the right list.**  Each left element pairs
against the right list only through `countBelowThreshold`, which the multiset-preserving adjacent swap fixes
(`countBelowThreshold_swap_adjacent`); the recursion carries the invariance down the left list. -/
theorem crossInversionCount_swap_adjacent {α : Type u} (slotValue : α → Nat)
    (firstCell secondCell : α) (rest : List α) :
    ∀ prefixCells : List α,
      crossInversionCount slotValue prefixCells (firstCell :: secondCell :: rest)
        = crossInversionCount slotValue prefixCells (secondCell :: firstCell :: rest)
  | [] => rfl
  | head :: tail => by
      show countBelowThreshold slotValue (slotValue head) (firstCell :: secondCell :: rest)
            + crossInversionCount slotValue tail (firstCell :: secondCell :: rest)
        = countBelowThreshold slotValue (slotValue head) (secondCell :: firstCell :: rest)
            + crossInversionCount slotValue tail (secondCell :: firstCell :: rest)
      rw [countBelowThreshold_swap_adjacent slotValue (slotValue head) firstCell secondCell rest,
          crossInversionCount_swap_adjacent slotValue firstCell secondCell rest tail]

/-- **The cross-inversion count only grows when an adjacent pair is inserted into the right list.**  Deleting the
pair from the right list can only decrease each left element's below-threshold count
(`countBelowThreshold_le_cons2`); the recursion sums the monotonicity down the left list. -/
theorem crossInversionCount_le_delete2 {α : Type u} (slotValue : α → Nat)
    (firstCell secondCell : α) (rest : List α) :
    ∀ prefixCells : List α,
      crossInversionCount slotValue prefixCells rest
        ≤ crossInversionCount slotValue prefixCells (firstCell :: secondCell :: rest)
  | [] => Nat.le_refl 0
  | head :: tail => by
      show countBelowThreshold slotValue (slotValue head) rest
            + crossInversionCount slotValue tail rest
        ≤ countBelowThreshold slotValue (slotValue head) (firstCell :: secondCell :: rest)
            + crossInversionCount slotValue tail (firstCell :: secondCell :: rest)
      exact Nat.add_le_add
        (countBelowThreshold_le_cons2 slotValue (slotValue head) firstCell secondCell rest)
        (crossInversionCount_le_delete2 slotValue firstCell secondCell rest tail)

/-! ## The prefixed strict-decrease facts (COMMUTE / STRAIGHTEN at arbitrary depth) -/

/-- ★ **The COMMUTE strict drop at arbitrary depth.**  Swapping an adjacent descending pair `bigger :: smaller`
(`slotValue smaller < slotValue bigger`) located behind ANY prefix strictly drops the inversion count: the
append homomorphism factors off the prefix (its own inversions unchanged, its cross term against the pair fixed by
`crossInversionCount_swap_adjacent`), and the within-suffix count drops by the shipped head fact
`countInversions_swap_adjacent_lt`. -/
theorem countInversions_prefixSwap_lt {α : Type u} (slotValue : α → Nat) (prefixCells : List α)
    {biggerCell smallerCell : α} (descending : slotValue smallerCell < slotValue biggerCell)
    (rest : List α) :
    countInversions slotValue (prefixCells ++ smallerCell :: biggerCell :: rest)
      < countInversions slotValue (prefixCells ++ biggerCell :: smallerCell :: rest) := by
  rw [countInversions_append slotValue prefixCells (smallerCell :: biggerCell :: rest),
      countInversions_append slotValue prefixCells (biggerCell :: smallerCell :: rest),
      crossInversionCount_swap_adjacent slotValue smallerCell biggerCell rest prefixCells]
  exact Nat.add_lt_add_right
    (Nat.add_lt_add_left (countInversions_swap_adjacent_lt slotValue descending rest)
      (countInversions slotValue prefixCells))
    (crossInversionCount slotValue prefixCells (biggerCell :: smallerCell :: rest))

/-- ★ **The STRAIGHTEN strict drop at arbitrary depth.**  Deleting an adjacent descending pair `bigger :: smaller`
(`slotValue smaller < slotValue bigger`, a genuine inversion) located behind ANY prefix strictly drops the
inversion count: the append homomorphism factors off the prefix, the within-suffix count drops by the shipped head
fact `countInversions_delete_head_lt`, and the prefix's cross term only shrinks under the delete
(`crossInversionCount_le_delete2`). -/
theorem countInversions_prefixDelete_lt {α : Type u} (slotValue : α → Nat) (prefixCells : List α)
    {biggerCell smallerCell : α} (descending : slotValue smallerCell < slotValue biggerCell)
    (rest : List α) :
    countInversions slotValue (prefixCells ++ rest)
      < countInversions slotValue (prefixCells ++ biggerCell :: smallerCell :: rest) := by
  rw [countInversions_append slotValue prefixCells rest,
      countInversions_append slotValue prefixCells (biggerCell :: smallerCell :: rest)]
  exact Nat.lt_of_lt_of_le
    (Nat.add_lt_add_right
      (Nat.add_lt_add_left (countInversions_delete_head_lt slotValue descending rest)
        (countInversions slotValue prefixCells))
      (crossInversionCount slotValue prefixCells rest))
    (Nat.add_le_add_left
      (crossInversionCount_le_delete2 slotValue biggerCell smallerCell rest prefixCells)
      (countInversions slotValue prefixCells
        + countInversions slotValue (biggerCell :: smallerCell :: rest)))

/-! ## Slot-congruence: replacing the located pair by slot-equal atoms preserves the count -/

/-- Two two-headed lists with pointwise-equal head slots have equal below-threshold count. -/
theorem countBelowThreshold_cons2_slotCongr {α : Type u} (slotValue : α → Nat) (threshold : Nat)
    {firstA secondA firstB secondB : α}
    (firstSlot : slotValue firstA = slotValue firstB) (secondSlot : slotValue secondA = slotValue secondB)
    (rest : List α) :
    countBelowThreshold slotValue threshold (firstA :: secondA :: rest)
      = countBelowThreshold slotValue threshold (firstB :: secondB :: rest) := by
  show (if slotValue firstA < threshold then 1 else 0)
        + ((if slotValue secondA < threshold then 1 else 0)
            + countBelowThreshold slotValue threshold rest)
    = (if slotValue firstB < threshold then 1 else 0)
        + ((if slotValue secondB < threshold then 1 else 0)
            + countBelowThreshold slotValue threshold rest)
  rw [firstSlot, secondSlot]

/-- Two two-headed lists with pointwise-equal head slots have equal cross-inversion count against any prefix. -/
theorem crossInversionCount_cons2_slotCongr {α : Type u} (slotValue : α → Nat)
    {firstA secondA firstB secondB : α}
    (firstSlot : slotValue firstA = slotValue firstB) (secondSlot : slotValue secondA = slotValue secondB)
    (rest : List α) :
    ∀ prefixCells : List α,
      crossInversionCount slotValue prefixCells (firstA :: secondA :: rest)
        = crossInversionCount slotValue prefixCells (firstB :: secondB :: rest)
  | [] => rfl
  | head :: tail => by
      show countBelowThreshold slotValue (slotValue head) (firstA :: secondA :: rest)
            + crossInversionCount slotValue tail (firstA :: secondA :: rest)
        = countBelowThreshold slotValue (slotValue head) (firstB :: secondB :: rest)
            + crossInversionCount slotValue tail (firstB :: secondB :: rest)
      rw [countBelowThreshold_cons2_slotCongr slotValue (slotValue head) firstSlot secondSlot rest,
          crossInversionCount_cons2_slotCongr slotValue firstSlot secondSlot rest tail]

/-- Two two-headed lists with pointwise-equal head slots have equal inversion count. -/
theorem countInversions_cons2_slotCongr {α : Type u} (slotValue : α → Nat)
    {firstA secondA firstB secondB : α}
    (firstSlot : slotValue firstA = slotValue firstB) (secondSlot : slotValue secondA = slotValue secondB)
    (rest : List α) :
    countInversions slotValue (firstA :: secondA :: rest)
      = countInversions slotValue (firstB :: secondB :: rest) := by
  show (if slotValue secondA < slotValue firstA then 1 else 0)
        + countBelowThreshold slotValue (slotValue firstA) rest
      + (countBelowThreshold slotValue (slotValue secondA) rest + countInversions slotValue rest)
    = (if slotValue secondB < slotValue firstB then 1 else 0)
        + countBelowThreshold slotValue (slotValue firstB) rest
      + (countBelowThreshold slotValue (slotValue secondB) rest + countInversions slotValue rest)
  rw [firstSlot, secondSlot]

/-- ★ **Replacing the located pair by slot-equal atoms preserves the inversion count.**  The append homomorphism
factors off the prefix; the within-suffix count and the prefix's cross term are each slot-congruent
(`countInversions_cons2_slotCongr` / `crossInversionCount_cons2_slotCongr`).  This is what lets a COMMUTE step see
through the swap's context re-threading: the moved atoms carry re-threaded boundary paths but the SAME cup/cap
tag, hence the same slot. -/
theorem countInversions_prefixCons2_slotCongr {α : Type u} (slotValue : α → Nat)
    {firstA secondA firstB secondB : α}
    (firstSlot : slotValue firstA = slotValue firstB) (secondSlot : slotValue secondA = slotValue secondB)
    (prefixCells rest : List α) :
    countInversions slotValue (prefixCells ++ firstA :: secondA :: rest)
      = countInversions slotValue (prefixCells ++ firstB :: secondB :: rest) := by
  rw [countInversions_append slotValue prefixCells (firstA :: secondA :: rest),
      countInversions_append slotValue prefixCells (firstB :: secondB :: rest),
      countInversions_cons2_slotCongr slotValue firstSlot secondSlot rest,
      crossInversionCount_cons2_slotCongr slotValue firstSlot secondSlot rest prefixCells]

/-! ## The spine specializations on the cup/cap tag -/

/-- ★ **The COMMUTE spine drop at arbitrary depth.**  Replacing a located cup·cap pair by a slot-preserving
cap·cup pair (the two moved atoms keep their tag: `capMoved` a cap, `cupMoved` a cup) strictly drops
`spineDisorder`.  The moved atoms are seen through by slot-congruence; the resulting literal transposition drops
by `countInversions_prefixSwap_lt` (a cap slots `0`, a cup slots `1`, so cup-then-cap is the descending
inversion). -/
theorem spineDisorder_swap_lt {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (prefixCells : List (SpineAtom signature sourceMode targetMode))
    {cupAtom capAtom capMoved cupMoved : SpineAtom signature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (isCapMoved : capMoved.isCupAtom = false) (isCupMoved : cupMoved.isCupAtom = true)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    spineDisorder (prefixCells ++ capMoved :: cupMoved :: rest)
      < spineDisorder (prefixCells ++ cupAtom :: capAtom :: rest) := by
  show countInversions (cupCapSlotValue SpineAtom.isCupAtom) (prefixCells ++ capMoved :: cupMoved :: rest)
    < countInversions (cupCapSlotValue SpineAtom.isCupAtom) (prefixCells ++ cupAtom :: capAtom :: rest)
  rw [countInversions_prefixCons2_slotCongr (cupCapSlotValue SpineAtom.isCupAtom)
        ((cupCapSlotValue_cap SpineAtom.isCupAtom isCapMoved).trans
          (cupCapSlotValue_cap SpineAtom.isCupAtom isCapCap).symm)
        ((cupCapSlotValue_cup SpineAtom.isCupAtom isCupMoved).trans
          (cupCapSlotValue_cup SpineAtom.isCupAtom isCupCup).symm)
        prefixCells rest]
  exact countInversions_prefixSwap_lt (cupCapSlotValue SpineAtom.isCupAtom) prefixCells
    (cupCapSlotValue_cap_lt_cup SpineAtom.isCupAtom isCapCap isCupCup) rest

/-- ★ **The STRAIGHTEN spine drop at arbitrary depth.**  Deleting a located cup·cap pair strictly drops
`spineDisorder` (the pair is a descending inversion — a cup slots `1`, the following cap `0`), by
`countInversions_prefixDelete_lt`. -/
theorem spineDisorder_delete_lt {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (prefixCells : List (SpineAtom signature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom signature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    spineDisorder (prefixCells ++ rest)
      < spineDisorder (prefixCells ++ cupAtom :: capAtom :: rest) := by
  show countInversions (cupCapSlotValue SpineAtom.isCupAtom) (prefixCells ++ rest)
    < countInversions (cupCapSlotValue SpineAtom.isCupAtom) (prefixCells ++ cupAtom :: capAtom :: rest)
  exact countInversions_prefixDelete_lt (cupCapSlotValue SpineAtom.isCupAtom) prefixCells
    (cupCapSlotValue_cap_lt_cup SpineAtom.isCupAtom isCapCap isCupCup) rest

/-! ## The `CellDescentResult` builders — reduce the oracle's per-step to `(next, stepConv)` -/

/-- ★ **The COMMUTE `CellDescentResult` builder.**  Given a `next` cell saturated-convertible to `cell` whose
spine is `cell`'s spine with the located cup·cap pair transposed to a slot-preserving cap·cup (the moved atoms
keep their tags), package a `CellDescentResult cell`: `disorderDrops` is discharged by `spineDisorder_swap_lt`.
The oracle's COMMUTE branch is thereby reduced to producing this `(next, stepConv)` — the chain-surgery reassembly
with the two atoms transposed and its Godement `saturatedGodementExchange` conversion. -/
def cellDescentResult_ofCommuteStep {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cell next : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (stepConv : SaturatedTwoCellConv cell next)
    (prefixCells rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {cupAtom capAtom capMoved cupMoved : SpineAtom adjunctionModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (isCapMoved : capMoved.isCupAtom = false) (isCupMoved : cupMoved.isCupAtom = true)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (targetSplit : next.spine = prefixCells ++ capMoved :: cupMoved :: rest) :
    CellDescentResult cell :=
  ⟨next, stepConv, by
    rw [sourceSplit, targetSplit]
    exact spineDisorder_swap_lt prefixCells isCupCup isCapCap isCapMoved isCupMoved rest⟩

/-- ★ **The STRAIGHTEN `CellDescentResult` builder.**  Given a `next` cell saturated-convertible to `cell` whose
spine is `cell`'s spine with the located cup·cap pair DELETED, package a `CellDescentResult cell`: `disorderDrops`
is discharged by `spineDisorder_delete_lt`.  The oracle's STRAIGHTEN branch is thereby reduced to producing this
`(next, stepConv)` — the chain-surgery reassembly with the collapsing partner pair removed and its
`snakeStraightensInContext` conversion (fed the partner-collapse witness). -/
def cellDescentResult_ofStraightenStep {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cell next : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (stepConv : SaturatedTwoCellConv cell next)
    (prefixCells rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjunctionModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (targetSplit : next.spine = prefixCells ++ rest) :
    CellDescentResult cell :=
  ⟨next, stepConv, by
    rw [sourceSplit, targetSplit]
    exact spineDisorder_delete_lt prefixCells isCupCup isCapCap rest⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the disorder half of the oracle's per-step is RIGOROUS at arbitrary depth, and the oracle's
per-step is reduced to producing `(next, stepConv)`.**  `countInversions_prefixSwap_lt` /
`countInversions_prefixDelete_lt` lift the shipped head strict-decrease facts to a redex behind any prefix (via
the append homomorphism, the cross-term swap-invariance / delete-monotonicity, and — for COMMUTE — the
slot-congruence `countInversions_prefixCons2_slotCongr` that sees through the swap's context re-threading).  Their
spine specializations `spineDisorder_swap_lt` / `spineDisorder_delete_lt` fire on the cup/cap tag, and the two
builders `cellDescentResult_ofCommuteStep` / `cellDescentResult_ofStraightenStep` package a `CellDescentResult`
from a `(next, stepConv)` and the source/target spine splits, discharging `disorderDrops`.

  What this marker does NOT claim — the `(next, stepConv)` production (the oracle's genuine residual, gates stay
  `false`):
  * COMMUTE — the chain-surgery `next` needs the disjoint-window swap at the boundary-PATH level (a
    `RealizedSpineChain` over the transposed word); the shipped `adjunctionSpineAtomSwap_of_disjointWindows` /
    `adjunctionSwappedPair_isBoundaryChained` realize it only at the flat boundary-LENGTH level;
  * STRAIGHTEN — the `snakeStraightensInContext` `stepConv` needs a collapse witness `cupFrame ⊟ capFrame ≈ id`
    that window-distance-1 does NOT supply (a shared-leg non-partner crossing), coupling to the arc non-crossing
    partner discipline lifted to the cell level and the deferred composite-1-cell whisker functoriality.

  So `CellDescentStepOracle` stays UN-inhabited; `MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3
  gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyRedexStepDrop : Bool := true

end FX1Poly.Polygraph
