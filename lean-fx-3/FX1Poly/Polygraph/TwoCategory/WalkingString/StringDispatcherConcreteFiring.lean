import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDegenerateSplit

/-! # WalkingString — the case-(a) DISPATCHER fired end-to-end on a concrete valley pair (FC-3 r13, B4)

The shipped case-(a) reducer `stringDegenerateEmptySource_of_widthZero` (`StringValleyDegenerateSplit`) discharges the
empty-source Tier-D branch: it block-splits both valleys, forces both cap blocks empty, re-reads the whole matching at
`matchingOfSpineList 0` on the cup suffixes, and hands off to the width-0 pure-cup sub-producer
`StringWidthZeroPureCupDeterminacyShared` (sub-producer (i)).  This file FIRES that dispatcher end-to-end on a
CONCRETE empty-source valley PAIR, confirming the whole case-(a) plumbing accepts real valleys:

  * ★ `stringCaseADispatcher_firesOnConcreteValleyPair` — two concrete empty-source valley cells at the `base→base·F·G`
    boundary (`sourcePath = id_base`, width 0): the lower cup `η = gen unitLower` and the same cup vertically composed
    with the identity 2-cell on `F·G` (a genuinely DIFFERENT cell with the same one-cup spine, hence the same
    `matchingOf`).  Given the width-0 sub-producer (i), the dispatcher runs its full case-(a) machinery (block-split →
    empty cap block → matching re-read → shared-top hand-off) and delivers the `SpineTraceEquiv` of the two spines.
    The `by rfl` discharges of the four side conditions (both valley predicates, the matching equality, the
    `sourcePath.length = 0`) confirm the concrete inputs land in the case-(a) branch.

## The sub-producer ledger (honest — no flag flips)

The dispatcher consumes the THREE named colour-keyed sub-producers factored in `StringValleyDegenerateSplit`.  Their
truth-state this round:

  * (i) `StringWidthZeroPureCupDeterminacyShared` — the width-0 pure-cup sort.  Its SINGLETON base case is discharged
    (`stringWidthZeroPureCupShared_singleton`, `StringWidthZeroCupSortBaseCase`); the full `∀`-inhabitation (the fueled
    partner-locate recursion) is the r14/r15 residual.  So this firing is CONDITIONAL on (i) — honest.
  * (ii) `StringMidZeroValleyTraceEquiv` — the mid-width-0 (cap-block) branch.  OPEN (the cap-dual of the width-0 sort;
    it now inherits the species precedent — the cap-side is mixed-species just as the cup-side, `StringWidthZeroMixedSpeciesWitness`).
  * (iii) `StringCellValleyTraceEquivPositive` — the doubly-positive main branch.  OPEN.

So `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) is NOT flipped — it stays `false`; this file
fires only the case-(a) dispatcher, conditional on sub-producer (i), on a concrete valley pair.

Raw Lean 4 + Init; the valleys are two literal `RawTwoCellExpr` constructors, the four side conditions by `rfl`, the
firing is one application of the shipped reducer.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/
`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The case-(a) dispatcher, fired on a concrete empty-source valley pair.**  Given the width-0 pure-cup
sub-producer (i), the shipped reducer `stringDegenerateEmptySource_of_widthZero` delivers the `SpineTraceEquiv` of two
concrete empty-source valley cells — the lower cup `η = gen unitLower` and that cup vcomp-ed with `id (F·G)` (a
different cell, same one-cup spine, same `matchingOf`).  The four case-(a) side conditions (both valley predicates, the
matching equality, `sourcePath.length = 0`) hold by `rfl`, so the concrete inputs land squarely in the empty-source
branch and the whole block-split → cap-empty → matching-reread → shared-top plumbing runs end-to-end. -/
theorem stringCaseADispatcher_firesOnConcreteValleyPair
    (widthZero : StringWidthZeroPureCupDeterminacyShared) :
    SpineTraceEquiv adjointTripleModeSignature
      (RawTwoCellExpr.gen StringTwoCell.unitLower).spine
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.gen StringTwoCell.unitLower)
        (RawTwoCellExpr.id stringFG)).spine := by
  refine stringDegenerateEmptySource_of_widthZero widthZero _ _ ?_ ?_ ?_ ?_ <;> rfl

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the case-(a) DISPATCHER fires end-to-end on a concrete valley pair (FC-3 r13, B4).**
`stringCaseADispatcher_firesOnConcreteValleyPair`: the shipped empty-source reducer
`stringDegenerateEmptySource_of_widthZero` runs its full case-(a) machinery (block-split, cap-block-empty,
matching-reread, shared-top hand-off) on two concrete empty-source valley cells and delivers their `SpineTraceEquiv`,
CONDITIONAL on the width-0 pure-cup sub-producer (i).  The four side conditions (both valley predicates, matching
equality, `sourcePath.length = 0`) discharge by `rfl`, confirming the concrete inputs land in the empty-source branch.

  Sub-producer ledger: (i) `StringWidthZeroPureCupDeterminacyShared` — singleton base case discharged
  (`StringWidthZeroCupSortBaseCase`), full inhabitation r14/r15; (ii) `StringMidZeroValleyTraceEquiv` — OPEN, now with
  the species precedent (`StringWidthZeroMixedSpeciesWitness`); (iii) `StringCellValleyTraceEquivPositive` — OPEN.  So
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays `false`, honestly — this fires only
  case (a), conditional on (i).  `= true`. -/
def fxString_hasDispatcherConcreteFiring : Bool := true

end FX1Poly.Polygraph
