import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedZigZagStraightening
import FX1Poly.Polygraph.Computad.WordProblem

/-! # SpineValleyDescent — the two loop invariants of the valley-normalization descent

The valley-normalization well-founded induction the fib-3 reconstruction assemble phase threads (progress
brick `hasAdjacentCupThenCap_of_not_valley_spine` locates an adjacent cup-then-cap pair; the shipped
`SaturatedZigZagStraightening` moves straighten or commute it) descends on a lexicographic measure whose
components are the boundary matching (a FIXED invariant) and the generator count (the STRICTLY DECREASING
component).  This file discharges the two named descent obligations the plan relies on, for each of the three
shipped moves, as reusable facts — leaving the assemble phase owing only its two genuinely-open inputs (the
`reify` base case and the spine-position-to-cell-subterm bridge, both recorded by the honesty marker).

  * ★ **`matchingOf` is a descent INVARIANT** — every straighten/commute move keeps the boundary matching fixed,
    consumed from the now-unconditional boundary-disciplined soundness
    (`saturatedConv_matchingOf_eq_ofBoundaryDiscipline` on the shipped `matchingSaturatedCongruence_proved`).
    So the matching is a loop invariant of the descent: the normal form the descent reaches shares its boundary
    matching with the source cell — exactly what the completeness reconstruction needs.
  * ★ **`generatorCount` STRICTLY DROPS** — every move removes precisely the collapsed snake's generator count
    (pure structural `Nat` arithmetic on the `RawTwoCellExpr.generatorCount` fold; the whiskers pass through, a
    `vcomp` sums, an `id` is zero).  So when the collapsed snake is non-trivial the measure strictly decreases,
    the well-foundedness of the descent.

Raw Lean 4 + Init; the invariance facts thread the shipped soundness, the count facts are `generatorCount`
`dsimp` + explicit `Nat.add_assoc`/`Nat.add_comm` (no `omega`, no AC-`simp`).  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Descent invariant 1 — the boundary matching is preserved by every move -/

/-- Every saturated move preserves the boundary matching — the unconditional boundary-disciplined soundness on
the shipped four-field congruence.  The loop invariant of the valley-normalization descent: whatever the
straighten/commute schedule, the cell it reaches shares its boundary matching with the source. -/
theorem matchingOf_invariant_ofSaturatedConv
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (conv : SaturatedTwoCellConv cellA cellB) : matchingOf cellA = matchingOf cellB :=
  saturatedConv_matchingOf_eq_ofBoundaryDiscipline matchingSaturatedCongruence_proved conv

/-- The in-context zig-zag straightening preserves the boundary matching. -/
theorem matchingOf_invariant_underZigzagStraighten {modeA modeB : AdjunctionMode}
    {pathF pathG pathH : ModalityPath adjunctionGraph modeA modeB}
    (snake : RawTwoCellExpr adjunctionModeSignature pathG pathG)
    (collapses : SaturatedTwoCellConv snake
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) pathG))
    (pre : RawTwoCellExpr adjunctionModeSignature pathF pathG)
    (post : RawTwoCellExpr adjunctionModeSignature pathG pathH) :
    matchingOf (RawTwoCellExpr.vcomp pre (RawTwoCellExpr.vcomp snake post))
      = matchingOf (RawTwoCellExpr.vcomp pre post) :=
  matchingOf_invariant_ofSaturatedConv (zigzagStraightensInVcompContext snake collapses pre post)

/-- The whiskered zig-zag collapse preserves the boundary matching (the fully-whiskered snake and the identity
it collapses to share their matching). -/
theorem matchingOf_invariant_underWhiskeredZigzag {modeLeft modeA modeB modeRight : AdjunctionMode}
    (wl : ModalityPath adjunctionGraph modeLeft modeA)
    (wr : ModalityPath adjunctionGraph modeB modeRight)
    {pathG : ModalityPath adjunctionGraph modeA modeB}
    (snake : RawTwoCellExpr adjunctionModeSignature pathG pathG)
    (collapses : SaturatedTwoCellConv snake
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) pathG)) :
    matchingOf (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) wl
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) wr snake))
      = matchingOf (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (composePath wl (composePath pathG wr))) :=
  matchingOf_invariant_ofSaturatedConv (whiskeredZigZagCollapses wl wr snake collapses)

/-- The commute-past-disjoint-then-straighten move preserves the boundary matching. -/
theorem matchingOf_invariant_underDisjointCommute {modeA modeB modeC : AdjunctionMode}
    {fPath : ModalityPath adjunctionGraph modeA modeB}
    {gPath g'Path : ModalityPath adjunctionGraph modeB modeC}
    (snake : RawTwoCellExpr adjunctionModeSignature fPath fPath)
    (collapses : SaturatedTwoCellConv snake
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) fPath))
    (cellB : RawTwoCellExpr adjunctionModeSignature gPath g'Path) :
    matchingOf (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) gPath snake)
        (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) fPath cellB))
      = matchingOf (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) fPath cellB) :=
  matchingOf_invariant_ofSaturatedConv (snakeCommutesPastDisjointThenStraightens snake collapses cellB)

/-! ## Descent invariant 2 — the generator count strictly drops by the collapsed snake -/

/-- The rearrangement at the heart of the vcomp-context straighten's count drop: `pre + (snake + post)` regroups
to `(pre + post) + snake`.  Explicit `Nat` rewrites (no AC-`simp`, no `omega`). -/
private theorem natMoveMiddleToEnd (preCount snakeCount postCount : Nat) :
    preCount + (snakeCount + postCount) = (preCount + postCount) + snakeCount := by
  rw [Nat.add_comm snakeCount postCount, ← Nat.add_assoc]

/-- The in-context zig-zag straightening removes EXACTLY the collapsed snake's generator count: the straightened
cell `vcomp pre post` has `snake.generatorCount` fewer generators than `vcomp pre (vcomp snake post)`.  Pure
structural arithmetic on the `generatorCount` fold. -/
theorem generatorCount_zigzagStraighten_drop {modeA modeB : AdjunctionMode}
    {pathF pathG pathH : ModalityPath adjunctionGraph modeA modeB}
    (snake : RawTwoCellExpr adjunctionModeSignature pathG pathG)
    (pre : RawTwoCellExpr adjunctionModeSignature pathF pathG)
    (post : RawTwoCellExpr adjunctionModeSignature pathG pathH) :
    (RawTwoCellExpr.vcomp pre (RawTwoCellExpr.vcomp snake post)).generatorCount
      = (RawTwoCellExpr.vcomp pre post).generatorCount + snake.generatorCount := by
  show pre.generatorCount + (snake.generatorCount + post.generatorCount)
    = (pre.generatorCount + post.generatorCount) + snake.generatorCount
  exact natMoveMiddleToEnd pre.generatorCount snake.generatorCount post.generatorCount

/-- The whiskered zig-zag collapse removes EXACTLY the collapsed snake's generator count: the identity it lands
on has `0`, the fully-whiskered snake has `snake.generatorCount`. -/
theorem generatorCount_whiskeredZigzag_drop {modeLeft modeA modeB modeRight : AdjunctionMode}
    (wl : ModalityPath adjunctionGraph modeLeft modeA)
    (wr : ModalityPath adjunctionGraph modeB modeRight)
    {pathG : ModalityPath adjunctionGraph modeA modeB}
    (snake : RawTwoCellExpr adjunctionModeSignature pathG pathG) :
    (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) wl
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) wr snake)).generatorCount
      = (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (composePath wl (composePath pathG wr))).generatorCount + snake.generatorCount := by
  show snake.generatorCount = 0 + snake.generatorCount
  exact (Nat.zero_add snake.generatorCount).symm

/-- The commute-past-disjoint-then-straighten move removes EXACTLY the collapsed snake's generator count: the
surviving `whiskerLeft fPath cellB` has `cellB.generatorCount`, the source pair has `snake.generatorCount +
cellB.generatorCount`. -/
theorem generatorCount_disjointCommute_drop {modeA modeB modeC : AdjunctionMode}
    {fPath : ModalityPath adjunctionGraph modeA modeB}
    {gPath g'Path : ModalityPath adjunctionGraph modeB modeC}
    (snake : RawTwoCellExpr adjunctionModeSignature fPath fPath)
    (cellB : RawTwoCellExpr adjunctionModeSignature gPath g'Path) :
    (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) gPath snake)
        (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) fPath cellB)).generatorCount
      = (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) fPath cellB).generatorCount
        + snake.generatorCount := by
  show snake.generatorCount + cellB.generatorCount = cellB.generatorCount + snake.generatorCount
  exact Nat.add_comm snake.generatorCount cellB.generatorCount

/-- ★ **The descent strictly decreases** when the collapsed snake is non-trivial: for the vcomp-context
straighten, `0 < snake.generatorCount` gives `(vcomp pre post).generatorCount < (vcomp pre (vcomp snake
post)).generatorCount`.  The well-foundedness of the valley-normalization descent (the same strict drop holds
for the other two moves by their count-drop lemmas). -/
theorem generatorCount_zigzagStraighten_strictDrop {modeA modeB : AdjunctionMode}
    {pathF pathG pathH : ModalityPath adjunctionGraph modeA modeB}
    (snake : RawTwoCellExpr adjunctionModeSignature pathG pathG)
    (snakeNonTrivial : 0 < snake.generatorCount)
    (pre : RawTwoCellExpr adjunctionModeSignature pathF pathG)
    (post : RawTwoCellExpr adjunctionModeSignature pathG pathH) :
    (RawTwoCellExpr.vcomp pre post).generatorCount
      < (RawTwoCellExpr.vcomp pre (RawTwoCellExpr.vcomp snake post)).generatorCount := by
  rw [generatorCount_zigzagStraighten_drop snake pre post]
  exact Nat.lt_add_of_pos_right snakeNonTrivial

/-! ## Honesty marker -/

/-- **Honesty marker — the two valley-normalization descent invariants are DISCHARGED; the assemble phase owes
only reify + the spine-to-cell bridge.**  For each of the three shipped straighten/commute moves this file
proves (1) `matchingOf` is preserved (the descent's fixed lexicographic component, consumed from the
unconditional boundary-disciplined soundness) and (2) `generatorCount` drops by exactly the collapsed snake's
count, strictly when the snake is non-trivial (the descent's decreasing component).  Together with the progress
brick `hasAdjacentCupThenCap_of_not_valley_spine` (a non-valley spine HAS an adjacent cup-then-cap pair) these
are the loop invariants a well-founded valley-normalization descent threads.

  What this marker does NOT claim — the two GENUINELY OPEN inputs the assemble phase still owes, neither
  supplied here:
  * the **`reify` base case** — a matching-only `canonicalCellOf` (a well-typed valley `RawTwoCellExpr` built
    from the boundary matching) with `matchingOf (reify m) = m`, so the descent's terminal valley is
    saturated-convertible to `reify (matchingOf valley)`.  No `reify` term exists anywhere; building it inverts
    the untyped `DiagramType` partner-list back to a well-typed valley, which loses the L/R modality typing (the
    tip-variance snag).  This is the reconstruction residual `MatchingStaircaseReconstructs` /
    `fxMode_hasArcCellReconstruction = false`, refuted at the general signature and open at the seed.
  * the **spine-position-to-cell-subterm bridge** — the progress brick locates the cup-then-cap pair in the
    SPINE (a `List (SpineAtom …)`), whereas the shipped moves act on the CELL tree; recovering a `vcomp`/whisker
    decomposition exhibiting the located pair as a straighten/commute redex is not built here.

  So this marker establishes the descent's STEP is sound (matching-preserving) and well-founded
  (count-decreasing); it does NOT close the reconstruction — the two open inputs above are unchanged, and the
  fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyDescentInvariants : Bool := true

end FX1Poly.Polygraph
