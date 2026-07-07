import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision

/-! # ArcStuckSpineNonSingleton — the STUCK case of the mixed reconstruction is NOT arc-singleton

The mixed cup/cap arc-reconstruction (`ArcCellReconstruction`) was to be attacked by a structural
DICHOTOMY on a non-empty mixed chained spine:

  * (a) a **boundary cup** (a cup whose two legs form a top-boundary partner pair) — bubble it right to
    LAST and peel (route D, `mixedSpine_lastCup_isShortChord` + `dropLastCup_arc_injective`);
  * (b) a **seed cap** (a cap consuming two bottom-boundary ports) — bubble it left to FIRST and peel
    (`spineArcHeadExtractionChained_ofCapArity`);
  * (c) otherwise the spine is **STUCK/closed** (first atom a cup, last atom a cap, but no boundary cup
    and no seed cap), the RESIDUAL.

The head-first routes need the REFUTED cup-head extraction (`headCupWindowReadoff_isFalse`, R1c), so the
whole point of routes (a)/(b) is to NEVER peel a cup head — they only peel a cup at the LAST slot or a cap
at the FIRST slot.  The hope was that the STUCK case (c) collapses trivially: that among stuck spines each
`FullArcStructure` value has a UNIQUE (singleton) stuck spine, so `arcStructureOf a = arcStructureOf b`
forces `a = b` on the nose and the reconstruction closes by `refl`.

**This file KILLS that hope with a machine-checked witness.**  Over the bottom boundary `left` (one wire)
there are two DISTINCT stuck spines — the DOUBLE snake `[cup@0, cap@1, cup@0, cap@1]` (two zig-zags stacked
in sequence, `doubleSnakeOnLeft`) and the NESTED snake `[cup@0, cup@2, cap@3, cap@1]` (one zig-zag inside
the other, `nestedSnakeOnLeft`) — that share the ENTIRE `FullArcStructure` (same `diagram` partner `[1,0]`,
same totals `2` cups / `2` caps, same `internalCupCounts` / `internalCapCounts` `[2,2]`).  Both are
rigorously STUCK: `diagram.bottomCount = 1` forbids a seed cap (a seed cap consumes TWO bottom ports),
`diagram.topCount = 1` forbids a boundary cup (a boundary cup needs TWO top ports for its leg pair), the
first atom is a cup (`(0,0,2)`) and the last atom is a cap (`(1,2,0)`).  So neither dichotomy peel applies,
yet the arc structure does NOT pin the spine.

## What this settles for the dichotomy route

The stuck case (c) is a GENUINE residual, not a `refl`: `arcStructureOf` is NOT injective on stuck spines.
So the dichotomy ISOLATES the reconstruction's hard core into the stuck case but does NOT bypass it — the
residual carries exactly the "sequential vs nested arches" planar-isotopy content (proving two closed
arc-equal configurations trace-equivalent), the same difficulty the leg-aligned re-selection
`arcCupReselection_exists` route already targets.  The `2`-atom snake IS a singleton (mode-rigidity on the
word `left`: a cup can only seat at a `base`-point — window `0` — and a cap only at a `tip` R·L adjacency —
window `1` — so `[cup@0, cap@1]` is the unique typeable `2`-atom stuck spine), so non-uniqueness first
appears at `4` atoms, exactly when two independent zig-zags can nest or sequence.

This does NOT refute the reconstruction: the double and nested snakes ARE trace-equivalent (arc structure is
a SOUND trace invariant, and they have equal arc structure), so `arcStructureOf a = arcStructureOf b ->
SpineTraceEquiv a b` is untouched — only the optimistic "stuck ⟹ singleton ⟹ refl" shortcut dies.

Raw Lean 4 + Init; the arc equality closes by kernel `decide` on the computable arc fold, the readoffs /
port counts by `rfl`, the distinctness by `rfl` readoffs + `decide` on the differing atom lists.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

open AdjunctionMode AdjunctionModality

/-! ## The two stuck witness cells over the boundary `left` -/

/-- The **nested** snake on `left`: snake the through-strand of the outer snake.  Concretely
`(left ◁ counit) ∘ ((left·right) ◁ snakeOnLeft) ∘ (unit ▷ left) : left ⇒ left` — an outer zig-zag with a
second zig-zag seated INSIDE its trailing strand.  Its spine is `[cup@0, cup@2, cap@3, cap@1]`, four atoms,
distinct from the double snake's `[cup@0, cap@1, cup@0, cap@1]`. -/
def nestedSnakeOnLeft :
    RawTwoCellExpr adjunctionModeSignature adjunctionLeftPath adjunctionLeftPath :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.vcomp snakeUnitWhisker
      (RawTwoCellExpr.whiskerLeft adjunctionLeftThenRight snakeOnLeft))
    snakeCounitWhisker

/-! ## Both are four-atom, cup-headed, cap-tailed spines -/

/-- The double snake's atoms as `(window, dom arity, cod arity)`: `[cup@0, cap@1, cup@0, cap@1]`.  First
atom is a cup (`(0,0,2)`), last atom is a cap (`(1,2,0)`). -/
theorem doubleSnake_atomReadoff :
    doubleSnakeOnLeft.spine.map
      (fun atom => (atom.leftContext.length, atom.generatorDom.length, atom.generatorCod.length))
      = [(0, 0, 2), (1, 2, 0), (0, 0, 2), (1, 2, 0)] := rfl

/-- The nested snake's atoms as `(window, dom arity, cod arity)`: `[cup@0, cup@2, cap@3, cap@1]`.  First
atom is a cup (`(0,0,2)`), last atom is a cap (`(1,2,0)`) — same endpoints, DIFFERENT middle. -/
theorem nestedSnake_atomReadoff :
    nestedSnakeOnLeft.spine.map
      (fun atom => (atom.leftContext.length, atom.generatorDom.length, atom.generatorCod.length))
      = [(0, 0, 2), (2, 0, 2), (3, 2, 0), (1, 2, 0)] := rfl

/-! ## Both are rigorously STUCK: one bottom port, one top port -/

/-- The double snake's boundary has ONE bottom port (so NO seed cap — a seed cap consumes two bottom
ports) and ONE top port (so NO boundary cup — a boundary cup needs two top ports for its leg pair). -/
theorem doubleSnake_isStuckByPorts :
    (arcStructureOfSpineList 1 doubleSnakeOnLeft.spine).diagram.bottomCount = 1
      ∧ (arcStructureOfSpineList 1 doubleSnakeOnLeft.spine).diagram.topCount = 1 := ⟨rfl, rfl⟩

/-- The nested snake's boundary has ONE bottom port and ONE top port — so it too is STUCK: no seed cap, no
boundary cup. -/
theorem nestedSnake_isStuckByPorts :
    (arcStructureOfSpineList 1 nestedSnakeOnLeft.spine).diagram.bottomCount = 1
      ∧ (arcStructureOfSpineList 1 nestedSnakeOnLeft.spine).diagram.topCount = 1 := ⟨rfl, rfl⟩

/-! ## The two stuck spines are DISTINCT, yet share the ENTIRE arc structure -/

/-- ★ **The two stuck spines are DISTINCT** — their second atoms differ (a cap `(1,2,0)` in the double
snake vs a cup `(2,0,2)` in the nested snake), read straight off the atom windows/arities. -/
theorem stuckSpines_distinct : doubleSnakeOnLeft.spine ≠ nestedSnakeOnLeft.spine := by
  intro spinesEqual
  have readoffsEqual :
      ([(0, 0, 2), (1, 2, 0), (0, 0, 2), (1, 2, 0)] : List (Nat × Nat × Nat))
        = [(0, 0, 2), (2, 0, 2), (3, 2, 0), (1, 2, 0)] := by
    rw [← doubleSnake_atomReadoff, spinesEqual, nestedSnake_atomReadoff]
  exact absurd readoffsEqual (by decide)

set_option maxHeartbeats 4000000 in
/-- ★ **The two stuck spines share the ENTIRE `FullArcStructure`.**  Same `diagram` (partner `[1,0]`, no
loops), same cup/cap totals (`2` / `2`), and the SAME `internalCupCounts` / `internalCapCounts` (`[2,2]`).
So `arcStructureOf` is NOT injective on stuck spines — the STUCK case of the dichotomy is a genuine
RESIDUAL, not a `refl`. -/
theorem stuckSpines_arcStructure_eq :
    arcStructureOfSpineList 1 doubleSnakeOnLeft.spine
      = arcStructureOfSpineList 1 nestedSnakeOnLeft.spine := by
  decide +kernel

/-! ## Honesty marker -/

/-- **Honesty marker — the STUCK case is NOT arc-singleton (the dichotomy isolates but does not bypass the
reconstruction).**  Two DISTINCT (`stuckSpines_distinct`) four-atom spines over the boundary `left`, both
STUCK — one bottom port / one top port (`doubleSnake_isStuckByPorts` / `nestedSnake_isStuckByPorts`, so no
seed cap and no boundary cup), cup-headed and cap-tailed (`doubleSnake_atomReadoff` /
`nestedSnake_atomReadoff`) — share the WHOLE `FullArcStructure` (`stuckSpines_arcStructure_eq`).  Hence
`arcStructureOf` is NOT injective on stuck spines: the dichotomy's STUCK residual carries the reconstruction's
full "sequential vs nested arches" planar-isotopy content, NOT a `refl` collapse.  What this marker does NOT
claim: any refutation of the reconstruction itself (the double and nested snakes ARE trace-equivalent, arc
structure being a sound trace invariant), only the death of the "stuck ⟹ singleton ⟹ refl" shortcut.
`= true`. -/
def fxMode_hasArcStuckSpineNonSingleton : Bool := true

end FX1Poly.Polygraph
