import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFoldLoops
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingDistinct
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWellFormedFoldWidth
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWellFormedFoldAssembly
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldGlue

/-! # BRAUER r31 — THE BOUNDARY-WORD LOOPS FIELD: `foldRealizesTargetDiagramCorrected` for `0 < bottomCount`

The r30 grand ledger reduced the sole open field of T-CLOSE(b) — `F.loops = d.loops` — to a mechanical fold-and-weld
assembly of the shipped per-step loops lemmas.  Every per-step fact is on the shelf:

  * (D1) `stepWiring_crossing_loops_zero` — an in-range crossing closes no loop (readback re-export).
  * `stepWiring_cup_loops` — a cup at position `0` closes no loop (freshness only); generalized here to any position
    (`stepWiring_cup_loops_atPos`, the input slice is empty for a `0 ⇒ 2` generator, so the trace is
    position-independent).
  * (C1) `stepWiring_cap_loops_ofDistinct` — a cap on a component-distinct head pair closes no loop.
  * (C2) `brauerOpenEndsDistinct_stepWiringCap` / (X) `brauerOpenEndsDistinct_stepWiringCrossing` — the zero-loops
    invariant `BrauerOpenEndsDistinct` survives caps (consuming its head) and crossings (window transposition).
  * `circleFold_loops` — `(processBrauer state (circleWord n)).loops = state.loops + n`.

This file WELDS them along the six-phase split `standardFormFold_appendSplit`:

    crossingWord bottomPerm ++ capWord capBlock ++ crossingWord middle
      ++ cupWord cupBlock ++ crossingWord topPerm ++ circleWord loops.

## The TWO-invariant flow (the one real subtlety)

There are TWO carriers, threaded separately:

  * **Freshness bundle** (`BrauerStateConditions`: `WiringDescStateFresh` + `isUnionFindForest` + `0 < nextFresh`) —
    the UNIVERSAL carrier, held at the seed for `0 < bottomCount` and preserved by EVERY phase
    (`brauerStateConditions_processBrauer`).  This is what the crossing / cup loops-zero and `circleFold_loops` ride.
  * **Component distinctness** (`BrauerOpenEndsDistinct`) — live and load-bearing ONLY on the seed → cap prefix: held
    at the seed (S), PRESERVED by the bottom crossings (X, `crossingWord_preserves_distinct`), and CONSUMED-and-
    RESTORED by the caps (C1 reads it for `+0`, C2 restores it).  The cup phase BREAKS it (a cup prepends a joined
    fresh pair), but no cap follows, so it is simply abandoned after phase 2.

So the boundary word closes ZERO loops (every cap fires on a distinct pair, every cup/crossing on fresh legs), and the
circle block adds exactly `loops = d.loops`.  Fed into the r29 gated close
`foldRealizesTargetDiagramCorrected_ofLoopsField`, this UNCONDITIONALLY discharges
`foldRealizesTargetDiagramCorrected d` for every well-formed boundary involution with `0 < d.bottomCount` — the
extraction close, and the four reconstruction masters' verbatim demand.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## B1 — THE THREE PHASE-ZEROS, truth-probed by evaluation FIRST

Before the general folds are proved, the kernel confirms on the two recon self-attacks that every boundary phase
(bottom crossing, cap, middle crossing, cup, top crossing) leaves the loop count at `0`, and only the circle block
lifts it to `d.loops`.  The monster (`bottomCount 6`, no crossings, two caps + two interior cups + one circle) and
adversarial-B (`bottomCount 3`, WITH crossings in `bottomPerm`/`topPerm`, one cap + one cup + one circle) between
them exercise all five boundary phases plus the circle. -/

/-- ★ **Phase-zero probe (monster).**  The six phase-boundary loop counts of the monster's corrected word are
`(0, 0, 0, 0, 0, 0)` on the seed → bottom-crossing → cap → middle-crossing → cup → top-crossing prefix (the circle
block then adds `d.loops = 1`).  Every boundary phase adds zero loops — read straight off the kernel. -/
theorem boundaryPhaseLoops_probe_monster :
    let form := reconstructStandardFormExt5Corrected monsterDiagram
    let s0 := brauerSeed monsterDiagram.bottomCount
    let s1 := processBrauer s0 (crossingWord form.bottomPerm)
    let s2 := processBrauer s1 (capWord form.capBlock)
    let s3 := processBrauer s2 (crossingWord form.middle)
    let s4 := processBrauer s3 (cupWord form.cupBlock)
    let s5 := processBrauer s4 (crossingWord form.topPerm)
    (s0.loops, s1.loops, s2.loops, s3.loops, s4.loops, s5.loops) = (0, 0, 0, 0, 0, 0) := by decide

/-- ★ **Phase-zero probe (adversarial-B, WITH crossings).**  Same for adversarial-B, whose `bottomPerm = [1]` and
`topPerm = [0]` genuinely fire crossings that re-represent bottom feet with fresh ids yet close no loop and preserve
component distinctness into the cap phase (`a1` reads `[0, 3, 4]`, three distinct components).  The five boundary
phases leave the loop count at `0`; the circle block then adds `d.loops = 1`. -/
theorem boundaryPhaseLoops_probe_adversarialB :
    let form := reconstructStandardFormExt5Corrected adversarialBDiagram
    let s0 := brauerSeed adversarialBDiagram.bottomCount
    let s1 := processBrauer s0 (crossingWord form.bottomPerm)
    let s2 := processBrauer s1 (capWord form.capBlock)
    let s3 := processBrauer s2 (crossingWord form.middle)
    let s4 := processBrauer s3 (cupWord form.cupBlock)
    let s5 := processBrauer s4 (crossingWord form.topPerm)
    (s0.loops, s1.loops, s2.loops, s3.loops, s4.loops, s5.loops) = (0, 0, 0, 0, 0, 0) := by decide

/-- ★ **The circle block lifts the boundary-zero to `d.loops`.**  On both witnesses the full six-phase fold (boundary
word then circle block) reaches exactly `d.loops` — the whole loops field, probed. -/
theorem boundaryPhaseLoops_probe_circleLift :
    (processBrauer (brauerSeed monsterDiagram.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected monsterDiagram))).loops
      = monsterDiagram.loops
      ∧ (processBrauer (brauerSeed adversarialBDiagram.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))).loops
      = adversarialBDiagram.loops :=
  ⟨by decide, by decide⟩

/-! ## B1 — the honesty marker for the re-export + probes -/

/-- ★ **Honesty marker — the (D1) crossing loops-zero re-export + the three phase-zeros are truth-probed (r31 B1).**
`stepWiring_crossing_loops_zero` (`Brauer/WiringDescBrauerReadback.lean`) publicly exports the private crossing
loops-zero step, and `boundaryPhaseLoops_probe_monster` / `_adversarialB` confirm by kernel evaluation that every
boundary phase (bottom crossing, cap, middle crossing, cup, top crossing) leaves the loop count at `0` on both recon
self-attacks, with the circle block lifting it to `d.loops` (`boundaryPhaseLoops_probe_circleLift`).  This is the
probe-first discipline for the general boundary-word loops-zero fold; the general lemmas land in B2, so no master
flips at B1.  `= true`. -/
def fxBrauer_hasBoundaryPhaseLoopsProbe : Bool := true

end FX1Poly.Polygraph
