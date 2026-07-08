import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellBridge
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellDriver

/-! # SpineValleyCellDegenerate — the Tier-D degenerate dispatch + the FULL `CellValleyTraceEquiv` lift
(Track B, Brick 4 close-out)

`SpineValleyCellBridge` shipped `cellValleyTraceEquiv_ofPositive` — two whole VALLEY cells with equal boundary
`matchingOf`, POSITIVE source width (`0 < sourcePath.length`) and POSITIVE mid-width
(`0 < survivorTopTotal (matchingOf valleyA)`, the through-strand count) are `SpineTraceEquiv`.  The FULL
`CellValleyTraceEquiv` (`SpineValleyCellDriver`) drops BOTH positivity hypotheses — it quantifies over the two
Tier-D degenerate valleys the positive branch misses:

  * **case (a) — `sourcePath.length = 0`** (empty source ⇒ empty cap block ⇒ the whole valley is a pure cup block
    from an empty seed).  The cap block is forced empty by the shipped `capBlockEmpty_ofSourceZero` (a cap fires at
    boundary `leftContext + 2 + rightContext ≥ 2 > 0`, impossible at width `0`), so both whole spines ARE their
    cup suffixes, boundary-chained at width `0`, with equal `matchingOfSpineList 0`.  This reduces DIRECTLY to the
    width-0 pure-cup determinacy.

  * **case (b) — `survivorTopTotal (matchingOf valleyA) = 0`** (mid-width `0`; the cap block consumes every bottom
    wire, so the cup blocks run from a width-0 mid-state).  This one is NOT a bare width-0 cup application: the
    shipped `valleysWithEqualMatching_spineTraceEquiv` hard-requires `0 < midWidth`, so case (b) additionally needs
    a mid-width-`0` block reassembly (cap-side `pureCapSpine_sort` under the cap arc-from-matching bridge +
    width-0 cup determinacy + `spineTraceEquiv_appendCongr` glue) — a genuine separate ingredient.

This file lands, all zero-axiom:

  * ★ **`WidthZeroPureCupDeterminacy`** — the crux width-0 brick, stated at the `matchingOf` (= `.diagram`) level
    so it is the exact consumer interface: two boundary-chained pure-cup spines over the width-`0` bottom boundary
    with equal `matchingOfSpineList 0` are `SpineTraceEquiv`.  This folds together the width-0 `arcDiagram_eq_matching`
    bridge, the `matchingOf → FullArcStructure` pure-cup determination, and `pureCupSpine_sort` at `bottomCount = 0`
    into ONE clean residual (its `ArcSwap*`-layer discharge is the standing hard node — see the marker).

  * ★ **`degenerateEmptySource_of_widthZero`** — case (a), FULLY PROVEN from `WidthZeroPureCupDeterminacy`: block-split
    both valleys, force both cap blocks empty (`capBlockEmpty_ofSourceZero`), read the two whole spines as their cup
    suffixes chained at width `0`, re-read the matching hypothesis at `matchingOfSpineList 0`, and apply the brick.

  * ★ **`MidZeroValleyTraceEquiv`** — case (b) residual hypothesis (the mid-width-`0` valley determinacy), stated at
    the cell level, isolating the block-reassembly ingredient the positive theorem cannot supply.

  * ★ **`cellValleyTraceEquiv_of_widthZero_of_midZero`** — the FULL LIFT: the three-way case split on
    `Nat.eq_zero_or_pos sourcePath.length` then on `Nat.eq_zero_or_pos (survivorTopTotal (matchingOf valleyA))`,
    dispatching the two degenerate branches to case (a) / case (b) and the doubly-positive branch to the shipped
    `cellValleyTraceEquiv_ofPositive`.  Given the two residual bricks, this yields the FULL `CellValleyTraceEquiv`
    UNCONDITIONALLY — the second residual of Piece II's reduction (`SpineValleyCellDriver`).

## What this file does NOT close — the two isolated residuals (no gate flag is flipped)

`CellValleyTraceEquiv` (hence Brick 4 R3 and the fib-3 gate) still reduces to exactly:
`WidthZeroPureCupDeterminacy` (the width-0 pure-cup brick — its arc-swap transposition atoms need a positive fresh
seed, `ArcSwapCorePackage.sigmaFixesZero` / `MatchingSwapStateConditions.nfPos`, genuinely FALSE at the width-0
seed where identifier `0` is a real cup leg colliding with the extract's `0` fallback sentinel) AND
`MidZeroValleyTraceEquiv` (the case-(b) mid-width-0 block reassembly).  Both are `ArcSwap*`/assembly-local, no new
mathematics, but genuine separate bricks.  This file makes the FULL lift rigorous and isolates the residual to
those two inputs.  `convOfMapEq` and the fib-3 gate flags stay `false`.

Raw Lean 4 + Init; pure block-split + case-split assembly over the shipped degenerate-structure lemma
`capBlockEmpty_ofSourceZero` and the positive-branch bridge, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The width-0 pure-cup determinacy — the crux Tier-D residual, at the `matchingOf` level -/

/-- ★ **The width-0 pure-cup determinacy brick.**  Two boundary-chained pure-cup spines over the width-`0` bottom
boundary with EQUAL `matchingOfSpineList 0` are `SpineTraceEquiv`.  Stated at the `matchingOf` (= `.diagram`) level
so it is exactly the consumer interface both Tier-D degenerate valleys need: it folds together the width-0
`arcDiagram_eq_matching` bridge, the `matchingOf → FullArcStructure` pure-cup determination, and `pureCupSpine_sort`
at `bottomCount = 0`.  Its discharge is the standing hard node — the arc-swap transposition atoms require a positive
fresh seed (`0 < nextFresh`), genuinely false at the width-0 seed where identifier `0` is a real cup leg (see the
honesty marker). -/
def WidthZeroPureCupDeterminacy : Prop :=
  ∀ {overallSource overallTarget : adjunctionGraph.Mode}
    (cupFirst cupSecond : List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
    AllCupArity cupFirst → AllCupArity cupSecond →
    SpineBoundaryChained 0 cupFirst → SpineBoundaryChained 0 cupSecond →
    matchingOfSpineList 0 cupFirst = matchingOfSpineList 0 cupSecond →
    SpineTraceEquiv adjunctionModeSignature cupFirst cupSecond

/-! ## Case (a) — an empty source boundary reduces to the width-0 cup brick -/

/-- ★ **Tier-D case (a), FULLY PROVEN from the width-0 brick.**  When `sourcePath.length = 0`, both valleys' cap
blocks are empty (`capBlockEmpty_ofSourceZero`), so the two whole spines ARE their cup suffixes — pure cups chained
at width `0` — and the whole-boundary `matchingOf` equality re-reads as a `matchingOfSpineList 0` equality of the
cup suffixes.  The width-0 pure-cup determinacy then delivers the `SpineTraceEquiv`. -/
theorem degenerateEmptySource_of_widthZero
    (widthZero : WidthZeroPureCupDeterminacy)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (valleyA valleyB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (isValleyA : isCapThenCupValley SpineAtom.isCupAtom valleyA.spine = true)
    (isValleyB : isCapThenCupValley SpineAtom.isCupAtom valleyB.spine = true)
    (matchingEq : matchingOf valleyA = matchingOf valleyB)
    (sourceZero : sourcePath.length = 0) :
    SpineTraceEquiv adjunctionModeSignature valleyA.spine valleyB.spine := by
  -- Block-split both valley spines into cap-prefix ++ cup-suffix.
  obtain ⟨capA, cupA, splitA, capPureA, cupPureA⟩ := spineValley_blockSplit valleyA.spine isValleyA
  obtain ⟨capB, cupB, splitB, capPureB, cupPureB⟩ := spineValley_blockSplit valleyB.spine isValleyB
  -- Both whole valleys are boundary-chained at width `0`.
  have chained0A : SpineBoundaryChained 0 (capA ++ cupA) := by
    have wholeChainedA : SpineBoundaryChained sourcePath.length (capA ++ cupA) := by
      rw [← splitA]; exact valleyA.spineBoundaryChained_spine
    rw [sourceZero] at wholeChainedA; exact wholeChainedA
  have chained0B : SpineBoundaryChained 0 (capB ++ cupB) := by
    have wholeChainedB : SpineBoundaryChained sourcePath.length (capB ++ cupB) := by
      rw [← splitB]; exact valleyB.spineBoundaryChained_spine
    rw [sourceZero] at wholeChainedB; exact wholeChainedB
  -- Force both cap blocks empty (a cap cannot fire at boundary `0`).
  have capEmptyA : capA = [] :=
    capBlockEmpty_ofSourceZero capA capPureA (spineBoundaryChained_prefix_ofAppend capA cupA 0 chained0A)
  have capEmptyB : capB = [] :=
    capBlockEmpty_ofSourceZero capB capPureB (spineBoundaryChained_prefix_ofAppend capB cupB 0 chained0B)
  -- The cup suffixes are boundary-chained at width `0`.
  have cupChained0A : SpineBoundaryChained 0 cupA := by rw [capEmptyA] at chained0A; exact chained0A
  have cupChained0B : SpineBoundaryChained 0 cupB := by rw [capEmptyB] at chained0B; exact chained0B
  -- Re-read the matching hypothesis at width `0` on the cup suffixes.
  have matchCupEq : matchingOfSpineList 0 cupA = matchingOfSpineList 0 cupB := by
    have eqA : matchingOf valleyA = matchingOfSpineList 0 cupA := by
      show matchingOfSpineList sourcePath.length valleyA.spine = matchingOfSpineList 0 cupA
      rw [sourceZero, splitA, capEmptyA]; rfl
    have eqB : matchingOf valleyB = matchingOfSpineList 0 cupB := by
      show matchingOfSpineList sourcePath.length valleyB.spine = matchingOfSpineList 0 cupB
      rw [sourceZero, splitB, capEmptyB]; rfl
    rw [← eqA, ← eqB]; exact matchingEq
  -- Apply the width-0 brick, transporting back through the block splits.
  rw [splitA, capEmptyA, splitB, capEmptyB]
  exact widthZero cupA cupB cupPureA cupPureB cupChained0A cupChained0B matchCupEq

/-! ## Case (b) — the mid-width-0 valley determinacy residual -/

/-- The Tier-D case-(b) residual hypothesis — two whole VALLEY cells with equal boundary `matchingOf`, POSITIVE
source width, and mid-width `0` (`survivorTopTotal (matchingOf valleyA) = 0`, the cap block consuming every bottom
wire) are `SpineTraceEquiv`.  Stated as a hypothesis because its discharge needs a mid-width-`0` block reassembly
(cap-side `pureCapSpine_sort` under the cap arc-from-matching bridge + the width-0 cup brick +
`spineTraceEquiv_appendCongr` glue) that the positive theorem `valleysWithEqualMatching_spineTraceEquiv` cannot
supply (it hard-requires `0 < midWidth`). -/
def MidZeroValleyTraceEquiv : Prop :=
  ∀ {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (valleyA valleyB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
    isCapThenCupValley SpineAtom.isCupAtom valleyA.spine = true →
    isCapThenCupValley SpineAtom.isCupAtom valleyB.spine = true →
    matchingOf valleyA = matchingOf valleyB →
    0 < sourcePath.length →
    survivorTopTotal (matchingOf valleyA) = 0 →
    SpineTraceEquiv adjunctionModeSignature valleyA.spine valleyB.spine

/-! ## The FULL `CellValleyTraceEquiv` lift -/

/-- ★ **The FULL cell-level Piece-II lift.**  The three-way case split closes `CellValleyTraceEquiv` for ALL valleys:
first on `Nat.eq_zero_or_pos sourcePath.length` (case (a) when zero, via `degenerateEmptySource_of_widthZero`), then
on `Nat.eq_zero_or_pos (survivorTopTotal (matchingOf valleyA))` (case (b) when zero, via `MidZeroValleyTraceEquiv`;
the doubly-positive branch via the shipped `cellValleyTraceEquiv_ofPositive`).  Given the two residual bricks, the
FULL `CellValleyTraceEquiv` — dropping BOTH positivity hypotheses of the positive branch — holds UNCONDITIONALLY. -/
theorem cellValleyTraceEquiv_of_widthZero_of_midZero
    (widthZero : WidthZeroPureCupDeterminacy) (midZero : MidZeroValleyTraceEquiv) :
    CellValleyTraceEquiv := by
  intro sourceMode targetMode sourcePath targetPath valleyA valleyB isValleyA isValleyB matchingEq
  cases Nat.eq_zero_or_pos sourcePath.length with
  | inl sourceZero =>
      exact degenerateEmptySource_of_widthZero widthZero valleyA valleyB isValleyA isValleyB matchingEq sourceZero
  | inr sourcePos =>
      cases Nat.eq_zero_or_pos (survivorTopTotal (matchingOf valleyA)) with
      | inl midZeroA =>
          exact midZero valleyA valleyB isValleyA isValleyB matchingEq sourcePos midZeroA
      | inr midPos =>
          exact cellValleyTraceEquiv_ofPositive valleyA valleyB isValleyA isValleyB matchingEq sourcePos midPos

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the FULL `CellValleyTraceEquiv` lift is rigorous and its residual is ISOLATED to exactly two
`ArcSwap*`/assembly-local bricks.**  `cellValleyTraceEquiv_of_widthZero_of_midZero` case-splits ALL valleys into the
doubly-positive branch (shipped `cellValleyTraceEquiv_ofPositive`) and the two Tier-D degenerate branches;
`degenerateEmptySource_of_widthZero` FULLY discharges case (a) (`sourcePath.length = 0`) from the width-0 pure-cup
determinacy, using the shipped `capBlockEmpty_ofSourceZero` to force both cap blocks empty and re-reading the
matching at width `0` on the cup suffixes.

  What this marker does NOT claim — the two isolated residuals (gates stay `false`):
  * `WidthZeroPureCupDeterminacy` — the width-0 pure-cup determinacy brick (`pureCupSpine_sort` +
    `arcDiagram_eq_matching` + the `matchingOf → FullArcStructure` pure-cup determination, all at `bottomCount = 0`).
    Its arc-swap transposition atoms need a positive fresh seed (`ArcSwapCorePackage.sigmaFixesZero`,
    `MatchingSwapStateConditions.nfPos`), genuinely FALSE at the width-0 seed where identifier `0` is a real cup leg
    colliding with the extract's `0` fallback sentinel — a genuine separate brick, not a wiring rung.
  * `MidZeroValleyTraceEquiv` — the case-(b) mid-width-`0` block reassembly (cap-side `pureCapSpine_sort` under the
    cap arc-from-matching bridge + the width-0 cup brick + `spineTraceEquiv_appendCongr` glue), the ingredient the
    positive `valleysWithEqualMatching_spineTraceEquiv` cannot supply.

  So the FULL `CellValleyTraceEquiv` (the second residual of `SpineValleyCellDriver`'s reduction of
  `MatchingReductsShareSpineTrace`) reduces to (width-0 pure-cup determinacy) AND (mid-width-0 reassembly), not to
  Piece II alone.  `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyCellDegenerate : Bool := true

end FX1Poly.Polygraph
