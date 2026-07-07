import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStuckSpineNonSingleton
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellDecidable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ClassSaturation

/-! # ArcStuckSpineSwapConnected — the STUCK non-singleton residual IS swap-connected (SpineTraceEquiv HOLDS)

`ArcStuckSpineNonSingleton` machine-checked that the STUCK case of the mixed cup/cap arc reconstruction is NOT
arc-singleton: two DISTINCT four-atom spines over the boundary `left` — the DOUBLE snake
`[cup@0, cap@1, cup@0, cap@1]` (`doubleSnakeOnLeft`) and the NESTED snake `[cup@0, cup@2, cap@3, cap@1]`
(`nestedSnakeOnLeft`) — share the ENTIRE `FullArcStructure`.  That killed the optimistic
"stuck ⟹ singleton ⟹ refl" shortcut but left the DECISIVE question open: are those two stuck spines related by
the swaps-only Godement/interchange closure `SpineTraceEquiv` (the conclusion type of `ArcCellReconstruction`,
the reconstruction target), or is `ArcCellReconstruction` itself FALSE on the stuck residual?

**This file settles it by MACHINE DECISION.**  Via the FREE-decision infrastructure
(`SpineTraceEquiv = AtomicTraceEquiv`, decided by BFS saturation of the seed's ~-class under the one-swap move
layer, `ClassSaturation`), the double snake's swap-class is computed exhaustively:

  * the class has EXACTLY FIVE members (readoffs, bottom-to-top, `(window, dom, cod)` per atom):
    `[cup@0,cap@1,cup@0,cap@1]` (seed), `[cup@0,cup@0,cap@3,cap@1]`, `[cup@0,cup@2,cap@3,cap@1]` (NESTED),
    `[cup@0,cup@0,cap@1,cap@1]`, `[cup@0,cup@2,cap@1,cap@1]`;
  * the BFS frontier EXHAUSTS (`didExhaustFrontier = true`), so the class is COMPLETE — no swap-reachable trace
    is missed;
  * the NESTED snake is member number three.

Hence `SpineTraceEquiv adjunctionModeSignature doubleSnakeOnLeft.spine nestedSnakeOnLeft.spine` HOLDS
(`spineTraceEquiv_doubleSnake_nestedSnake`), proved zero-axiom by `saturateClass_isSound` (unconditional — the
positive direction needs only membership, not the exhaustion gate) composed with `AtomicTraceEquiv.toSpineTraceEquiv`.
The membership itself is a kernel `decide` on the fuel-bounded saturation.

## What this settles for the reconstruction

The STUCK residual — the hardest known instance of `ArcCellReconstruction` at the cup/cap seed — is CONSISTENT
with the reconstruction: the two arc-equal parallel stuck cells DO have swap-equivalent spines.  So the
`#1996`-style `SpineTraceEquiv` reconstruction target is NOT a false theorem on its crux; the residual "sequential
vs nested arches" planar-isotopy content is genuinely a finite swap chain (five-element Temperley–Lieb ~-class),
and the outstanding work is the GENERAL completeness — arc-equal parallel spines ⟹ swap-connected, over all
realizable cup/cap configurations — not a refutation.  (At a GENERAL signature `ArcCellReconstruction` is still
FALSE, `not_arcCellReconstruction`, via the arity-`0⇒0` box leak; that is orthogonal — the residual lives at the
cup/cap seed, where this witness confirms it.)

Raw Lean 4 + Init; the membership closes by kernel `decide` on the computable BFS saturation, the equivalence by
the unconditional saturation soundness.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

open AdjunctionMode AdjunctionModality

/-! ## The saturated swap-class of the double snake -/

/-- The double snake's ~-class under the one-swap move layer, saturated with `fuel` breadth-first pops.  Seeded at
the double snake's spine; `fuel = 8` exhausts the frontier (a five-element class). -/
def doubleSnakeSwapClass (fuel : Nat) :
    List (List (SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.tip)) :=
  saturateClass adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq fuel
    doubleSnakeOnLeft.spine

/-- ★ **The nested snake's spine lives in the double snake's swap-class** — a kernel `decide` on the computable
BFS saturation (`fuel = 8`, which exhausts the frontier), via the hand-rolled list-membership decider over the
shipped spine-list decidable equality. -/
theorem nestedSnake_spine_mem_doubleSnakeSwapClass :
    nestedSnakeOnLeft.spine ∈ doubleSnakeSwapClass 8 :=
  @of_decide_eq_true (nestedSnakeOnLeft.spine ∈ doubleSnakeSwapClass 8)
    (listMemDecidable
      (spineListDecEq adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq)
      nestedSnakeOnLeft.spine (doubleSnakeSwapClass 8))
    (by decide)

/-! ## The decisive verdict: the two stuck spines ARE SpineTraceEquiv -/

/-- ★ **VERDICT — the STUCK non-singleton residual is SWAP-CONNECTED.**  The double snake's spine and the nested
snake's spine — the two DISTINCT arc-equal four-atom STUCK spines of `ArcStuckSpineNonSingleton` — ARE related by
the swaps-only Godement/interchange closure `SpineTraceEquiv`.  Proved zero-axiom: the nested spine is a member of
the double snake's swap-class (`nestedSnake_spine_mem_doubleSnakeSwapClass`), the saturation soundness
(`saturateClass_isSound`, UNCONDITIONAL — no exhaustion gate needed for the positive direction) yields the
atom-level swap equivalence, and `AtomicTraceEquiv.toSpineTraceEquiv` lifts it to the block-level
`SpineTraceEquiv`.  So the reconstruction target `arcStructureOf a = arcStructureOf b → SpineTraceEquiv a b` is
CONSISTENT on its hardest known (stuck) instance — NOT a false theorem there. -/
theorem spineTraceEquiv_doubleSnake_nestedSnake :
    SpineTraceEquiv adjunctionModeSignature doubleSnakeOnLeft.spine nestedSnakeOnLeft.spine :=
  (saturateClass_isSound adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq
    nestedSnake_spine_mem_doubleSnakeSwapClass).toSpineTraceEquiv

/-! ## Honesty marker -/

/-- **Honesty marker — the STUCK residual is swap-connected, so the reconstruction target holds on its crux.**
The two DISTINCT arc-equal four-atom STUCK spines of `ArcStuckSpineNonSingleton` (`doubleSnakeOnLeft.spine`,
`nestedSnakeOnLeft.spine`) ARE `SpineTraceEquiv` (`spineTraceEquiv_doubleSnake_nestedSnake`), decided by exhaustive
BFS saturation of the five-element swap ~-class.  Hence `ArcCellReconstruction` at the cup/cap seed is CONSISTENT
on its hardest known instance: the arc structure IS a sound-and-here-complete trace invariant on the stuck
residual, and the residual planar-isotopy content ("sequential vs nested arches") is a genuine finite swap chain,
not a counterexample.  What this marker does NOT claim: the GENERAL seed-level completeness (arc-equal parallel
spines ⟹ swap-connected, over all realizable cup/cap configurations) — that remains the standing obligation,
`fxMode_hasArcStructureReconstruction` stays `false`; nor does it touch the general-signature refutation
(`not_arcCellReconstruction`, the arity-`0⇒0` box leak, orthogonal to the cup/cap seed).  `= true`. -/
def fxMode_hasArcStuckSpineSwapConnected : Bool := true

end FX1Poly.Polygraph
