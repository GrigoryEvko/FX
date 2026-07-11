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

/-! ## B2 — the position-general cup loops-zero step

`stepWiring_cup_loops` (`Brauer/WiringDescCircleLoops.lean`) closes a cup at position `0`; the standard form's cup
block fires cups at the interior offset (`cupBlock = natReplicate _ throughCount`).  A cup is a `0 ⇒ 2` generator, so
its input slice `natListSliceAt openWires position 0` is empty for EVERY position — the decoded arc trace is the fresh
pair `(nextFresh, nextFresh + 1)` regardless of where the pair is inserted.  So the loops-zero proof is
position-independent; this is the same proof with `position` in place of `0`. -/

/-- ★ **A cup at ANY position closes no loop.**  The position only relocates the fresh pair in the open-wire list; the
arc trace (hence the loop delta) is the position-free fresh pair, which is never already connected
(`isSameComponent_freshPair_eq_false`, needing only that every link child is below `nextFresh`). -/
theorem stepWiring_cup_loops_atPos (state : WireState) (position : Nat)
    (childrenBounded : ∀ edge ∈ state.links, edge.1 < state.nextFresh) :
    (stepWiring state position cupWiring).loops = state.loops := by
  rw [stepWiring_loops_eq state position cupWiring]
  have htrace : wiringArcEvents (stepWiringInputNodes state position cupWiring)
        (stepWiringOutputNodes state cupWiring) cupWiring.inputCount cupWiring.arcs
      = [(state.nextFresh, state.nextFresh + 1)] := by
    show [(0 + state.nextFresh, 1 + state.nextFresh)] = [(state.nextFresh, state.nextFresh + 1)]
    rw [Nat.zero_add, Nat.add_comm 1 state.nextFresh]
  rw [htrace]
  show state.loops
      + ((isSameComponent state.links state.nextFresh (state.nextFresh + 1)).toNat
          + countJoinEventLoops [] (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)))
      + cupWiring.internalLoops = state.loops
  rw [isSameComponent_freshPair_eq_false state.nextFresh state.links childrenBounded state.nextFresh
    (Nat.le_refl _)]
  rfl

/-! ## B2 — the three phase loops-zero folds (D2 crossing, D3 cup, D4 cap) -/

/-- ★★ **(D2) A crossing staircase closes ZERO loops.**  Structural on `positions`: each in-range crossing closes no
loop (the (D1) re-export `stepWiring_crossing_loops_zero`), and the freshness bundle
(`WiringDescStateFresh` / forest / `0 < nextFresh`) is preserved to the next step
(`wiringDescStateFresh_stepWiring`, `stepWiring_links_isUnionFindForest`, `nextFresh` monotone).  The per-step window
fit is read off the `WellFormedBrauerFold` witness.  The loops-tracking mirror of `wellFormedBrauerFold_crossingWord`. -/
theorem crossingWord_loops_zero :
    (positions : List Nat) → (state : WireState) →
      WiringDescStateFresh state → isUnionFindForest state.links → 0 < state.nextFresh →
      WellFormedBrauerFold state (crossingWord positions) →
      (processBrauer state (crossingWord positions)).loops = state.loops
  | [], _state, _fresh, _forest, _nfPos, _wf => rfl
  | pos :: rest, state, fresh, forest, nfPos, wf => by
      obtain ⟨_gen, windowFit, wfRest⟩ := wf
      have hstep : (stepBrauerAtom state (crossingAt pos)).loops = state.loops :=
        stepWiring_crossing_loops_zero state pos fresh nfPos forest windowFit
      have fresh' : WiringDescStateFresh (stepBrauerAtom state (crossingAt pos)) :=
        wiringDescStateFresh_stepWiring state pos crossingWiring fresh nfPos
      have forest' : isUnionFindForest (stepBrauerAtom state (crossingAt pos)).links :=
        stepWiring_links_isUnionFindForest state pos crossingWiring forest
      have nfPos' : 0 < (stepBrauerAtom state (crossingAt pos)).nextFresh := by
        show 0 < (stepWiring state pos crossingWiring).nextFresh
        rw [stepWiring_nextFresh]; exact Nat.lt_of_lt_of_le nfPos (Nat.le_add_right _ _)
      have hcons : processBrauer state (crossingWord (pos :: rest))
          = processBrauer (stepBrauerAtom state (crossingAt pos)) (crossingWord rest) := rfl
      have hrec := crossingWord_loops_zero rest (stepBrauerAtom state (crossingAt pos)) fresh' forest' nfPos' wfRest
      rw [hcons, hrec, hstep]

/-- ★★ **(D3) A cup word closes ZERO loops.**  Structural on `positions`: each cup closes no loop
(`stepWiring_cup_loops_atPos`, freshness only — the link children are bounded by `fresh.2`), and freshness / `0 <
nextFresh` are preserved to the next step.  NO distinctness, NO window fit — a cup is a `0 ⇒ 2` generator that only
allocates a fresh pair. -/
theorem cupWord_loops_zero :
    (positions : List Nat) → (state : WireState) →
      WiringDescStateFresh state → 0 < state.nextFresh →
      (processBrauer state (cupWord positions)).loops = state.loops
  | [], _state, _fresh, _nfPos => rfl
  | pos :: rest, state, fresh, nfPos => by
      have hstep : (stepBrauerAtom state (cupAt pos)).loops = state.loops :=
        stepWiring_cup_loops_atPos state pos (fun edge edgeMem => (fresh.2 edge edgeMem).1)
      have fresh' : WiringDescStateFresh (stepBrauerAtom state (cupAt pos)) :=
        wiringDescStateFresh_stepWiring state pos cupWiring fresh nfPos
      have nfPos' : 0 < (stepBrauerAtom state (cupAt pos)).nextFresh := by
        show 0 < (stepWiring state pos cupWiring).nextFresh
        rw [stepWiring_nextFresh]; exact Nat.lt_of_lt_of_le nfPos (Nat.le_add_right _ _)
      have hcons : processBrauer state (cupWord (pos :: rest))
          = processBrauer (stepBrauerAtom state (cupAt pos)) (cupWord rest) := rfl
      have hrec := cupWord_loops_zero rest (stepBrauerAtom state (cupAt pos)) fresh' nfPos'
      rw [hcons, hrec, hstep]

/-- A list of open-wire count `≥ 2` decomposes as `firstWire :: secondWire :: rest` — the two-slot window a cap at
position `0` consumes.  `propext`-free (`Nat.not_succ_le_zero` on the short cases). -/
private theorem openWires_twoDecomp : (wires : List Nat) → 2 ≤ wires.length →
    ∃ firstWire secondWire rest, wires = firstWire :: secondWire :: rest
  | [], hlen => absurd hlen (Nat.not_succ_le_zero 1)
  | [_headWire], hlen => absurd (Nat.le_of_succ_le_succ hlen) (Nat.not_succ_le_zero 0)
  | firstWire :: secondWire :: rest, _hlen => ⟨firstWire, secondWire, rest, rfl⟩

/-- ★★ **(D4) The canonical cap block `capWord (natReplicate count 0)` closes ZERO loops.**  Structural on `count`,
threading the component-distinctness invariant `BrauerOpenEndsDistinct`: at each cap the window fit
(`WellFormedBrauerFold`) exposes the head pair `firstWire :: secondWire :: rest`, the invariant makes that pair
DISTINCT (positions `0 < 1`), so C1 (`stepWiring_cap_loops_ofDistinct`) closes no loop, and C2
(`brauerOpenEndsDistinct_stepWiringCap`) restores distinctness on the survivors.  The distinctness carrier is consumed
and restored at every cap — a cap never merges two survivors, so no cap in the block ever closes a loop. -/
theorem capWord_loops_zero_ofDistinct :
    (count : Nat) → (state : WireState) →
      isUnionFindForest state.links →
      BrauerOpenEndsDistinct state →
      WellFormedBrauerFold state (capWord (natReplicate count 0)) →
      (processBrauer state (capWord (natReplicate count 0))).loops = state.loops
  | 0, _state, _forest, _distinct, _wf => rfl
  | count + 1, state, forest, distinct, wf => by
      obtain ⟨_gen, windowFit, wfRest⟩ := wf
      have hlen : 2 ≤ state.openWires.length := windowFit
      obtain ⟨firstWire, secondWire, restWires, hopen⟩ := openWires_twoDecomp state.openWires hlen
      have oneBelow : 1 < state.openWires.length := Nat.lt_of_lt_of_le (by decide) hlen
      have distinctHead : isSameComponent state.links firstWire secondWire = false := by
        have h01 := distinct 0 1 (by decide) oneBelow
        rw [hopen] at h01
        exact h01
      have hstep : (stepBrauerAtom state (capAt 0)).loops = state.loops :=
        stepWiring_cap_loops_ofDistinct state firstWire secondWire restWires hopen distinctHead
      have forest' : isUnionFindForest (stepBrauerAtom state (capAt 0)).links :=
        stepWiring_links_isUnionFindForest state 0 capWiring forest
      have distinct' : BrauerOpenEndsDistinct (stepBrauerAtom state (capAt 0)) :=
        brauerOpenEndsDistinct_stepWiringCap state forest firstWire secondWire restWires hopen distinct
      have hcons : processBrauer state (capWord (natReplicate (count + 1) 0))
          = processBrauer (stepBrauerAtom state (capAt 0)) (capWord (natReplicate count 0)) := rfl
      have hrec := capWord_loops_zero_ofDistinct count (stepBrauerAtom state (capAt 0)) forest' distinct' wfRest
      rw [hcons, hrec, hstep]

/-! ## B2 — the distinctness carrier survives the bottom crossings (feeds the cap phase) -/

/-- ★★ **A crossing staircase PRESERVES component distinctness.**  Structural on `positions`: each in-range crossing
preserves `BrauerOpenEndsDistinct` (X, `brauerOpenEndsDistinct_stepWiringCrossing`, the window-transposition pullback),
and the freshness bundle threads to the next step.  This carries the seed distinctness (S) through the bottom crossing
phase and into the cap phase (D4). -/
theorem crossingWord_preserves_distinct :
    (positions : List Nat) → (state : WireState) →
      WiringDescStateFresh state → isUnionFindForest state.links → 0 < state.nextFresh →
      WellFormedBrauerFold state (crossingWord positions) →
      BrauerOpenEndsDistinct state →
      BrauerOpenEndsDistinct (processBrauer state (crossingWord positions))
  | [], _state, _fresh, _forest, _nfPos, _wf, distinct => distinct
  | pos :: rest, state, fresh, forest, nfPos, wf, distinct => by
      obtain ⟨_gen, windowFit, wfRest⟩ := wf
      have distinctStep : BrauerOpenEndsDistinct (stepBrauerAtom state (crossingAt pos)) :=
        brauerOpenEndsDistinct_stepWiringCrossing state fresh forest nfPos pos windowFit distinct
      have fresh' : WiringDescStateFresh (stepBrauerAtom state (crossingAt pos)) :=
        wiringDescStateFresh_stepWiring state pos crossingWiring fresh nfPos
      have forest' : isUnionFindForest (stepBrauerAtom state (crossingAt pos)).links :=
        stepWiring_links_isUnionFindForest state pos crossingWiring forest
      have nfPos' : 0 < (stepBrauerAtom state (crossingAt pos)).nextFresh := by
        show 0 < (stepWiring state pos crossingWiring).nextFresh
        rw [stepWiring_nextFresh]; exact Nat.lt_of_lt_of_le nfPos (Nat.le_add_right _ _)
      have hcons : processBrauer state (crossingWord (pos :: rest))
          = processBrauer (stepBrauerAtom state (crossingAt pos)) (crossingWord rest) := rfl
      rw [hcons]
      exact crossingWord_preserves_distinct rest (stepBrauerAtom state (crossingAt pos))
        fresh' forest' nfPos' wfRest distinctStep

/-! ## B2 — THE WELD: the boundary word closes zero loops, and the full loops field -/

/-- ★★★ **The loops field, over an arbitrary extended standard form.**  For a well-formed word whose cap block is the
canonical `natReplicate capCount 0`, the six-phase fold's loop count is exactly `form.loops`: the seed carries `0`
loops; the bottom crossings (D2) and the caps (D4, fed the seed distinctness through the crossings by
`crossingWord_preserves_distinct`) and the middle crossings (D2) and the interior cups (D3) and the top crossings (D2)
each close ZERO loops; and the circle block adds exactly `form.loops` (`circleFold_loops`).  The freshness bundle is
threaded through every phase by `brauerStateConditions_processBrauer`; distinctness is live only on the seed → cap
prefix (the cup phase breaks it, but no cap follows). -/
theorem foldLoopsField_ofForm (form : BrauerStandardFormExt5) (bottomPos : 0 < form.bottomCount)
    (capCount : Nat) (hCapBlock : form.capBlock = natReplicate capCount 0)
    (wfWord : WellFormedBrauerFold (brauerSeed form.bottomCount) (standardFormWordExt5 form)) :
    (processBrauer (brauerSeed form.bottomCount) (standardFormWordExt5 form)).loops = form.loops := by
  have conds0 : BrauerStateConditions form.bottomCount (brauerSeed form.bottomCount) :=
    brauerStateConditions_seed form.bottomCount bottomPos
  have distinct0 : BrauerOpenEndsDistinct (brauerSeed form.bottomCount) :=
    brauerOpenEndsDistinct_seed form.bottomCount
  have hword : standardFormWordExt5 form
      = crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
        ++ cupWord form.cupBlock ++ crossingWord form.topPerm ++ circleWord form.loops := rfl
  rw [hword] at wfWord
  -- peel the five boundary phase WF witnesses (at the prefix-append boundary states)
  obtain ⟨wf15, _wf6⟩ := wellFormedBrauerFold_appendSplit
    (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
      ++ cupWord form.cupBlock ++ crossingWord form.topPerm) (brauerSeed form.bottomCount)
    (circleWord form.loops) wfWord
  obtain ⟨wf14, wfTop⟩ := wellFormedBrauerFold_appendSplit
    (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
      ++ cupWord form.cupBlock) (brauerSeed form.bottomCount) (crossingWord form.topPerm) wf15
  obtain ⟨wf13, _wfCup⟩ := wellFormedBrauerFold_appendSplit
    (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle)
    (brauerSeed form.bottomCount) (cupWord form.cupBlock) wf14
  obtain ⟨wf12, wfMiddle⟩ := wellFormedBrauerFold_appendSplit
    (crossingWord form.bottomPerm ++ capWord form.capBlock)
    (brauerSeed form.bottomCount) (crossingWord form.middle) wf13
  obtain ⟨wfBottom, wfCap⟩ := wellFormedBrauerFold_appendSplit
    (crossingWord form.bottomPerm) (brauerSeed form.bottomCount) (capWord form.capBlock) wf12
  -- the freshness bundle at each prefix-append boundary state
  have conds1 : BrauerStateConditions form.bottomCount
      (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm)) :=
    brauerStateConditions_processBrauer form.bottomCount (crossingWord form.bottomPerm)
      (brauerSeed form.bottomCount) conds0
  have conds2 : BrauerStateConditions form.bottomCount
      (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm ++ capWord form.capBlock)) :=
    brauerStateConditions_processBrauer form.bottomCount
      (crossingWord form.bottomPerm ++ capWord form.capBlock) (brauerSeed form.bottomCount) conds0
  have conds3 : BrauerStateConditions form.bottomCount
      (processBrauer (brauerSeed form.bottomCount)
        (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle)) :=
    brauerStateConditions_processBrauer form.bottomCount
      (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle)
      (brauerSeed form.bottomCount) conds0
  have conds4 : BrauerStateConditions form.bottomCount
      (processBrauer (brauerSeed form.bottomCount)
        (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
          ++ cupWord form.cupBlock)) :=
    brauerStateConditions_processBrauer form.bottomCount
      (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
        ++ cupWord form.cupBlock) (brauerSeed form.bottomCount) conds0
  have conds5 : BrauerStateConditions form.bottomCount
      (processBrauer (brauerSeed form.bottomCount)
        (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
          ++ cupWord form.cupBlock ++ crossingWord form.topPerm)) :=
    brauerStateConditions_processBrauer form.bottomCount
      (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
        ++ cupWord form.cupBlock ++ crossingWord form.topPerm) (brauerSeed form.bottomCount) conds0
  -- the distinctness carrier reaches the cap phase (seed distinct, preserved by the bottom crossings)
  have distinct1 : BrauerOpenEndsDistinct
      (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm)) :=
    crossingWord_preserves_distinct form.bottomPerm (brauerSeed form.bottomCount)
      conds0.fresh conds0.forest conds0.nfPos wfBottom distinct0
  -- the boundary word closes zero loops, phase by phase
  have hp1 : (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm)).loops = 0 :=
    crossingWord_loops_zero form.bottomPerm (brauerSeed form.bottomCount)
      conds0.fresh conds0.forest conds0.nfPos wfBottom
  have hp2 : (processBrauer (brauerSeed form.bottomCount)
      (crossingWord form.bottomPerm ++ capWord form.capBlock)).loops = 0 := by
    rw [processBrauer_append (crossingWord form.bottomPerm) (brauerSeed form.bottomCount)
      (capWord form.capBlock), hCapBlock,
      capWord_loops_zero_ofDistinct capCount
        (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm))
        conds1.forest distinct1 (hCapBlock ▸ wfCap)]
    exact hp1
  have hp3 : (processBrauer (brauerSeed form.bottomCount)
      (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle)).loops = 0 := by
    rw [processBrauer_append (crossingWord form.bottomPerm ++ capWord form.capBlock)
      (brauerSeed form.bottomCount) (crossingWord form.middle),
      crossingWord_loops_zero form.middle
        (processBrauer (brauerSeed form.bottomCount)
          (crossingWord form.bottomPerm ++ capWord form.capBlock))
        conds2.fresh conds2.forest conds2.nfPos wfMiddle]
    exact hp2
  have hp4 : (processBrauer (brauerSeed form.bottomCount)
      (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
        ++ cupWord form.cupBlock)).loops = 0 := by
    rw [processBrauer_append
      (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle)
      (brauerSeed form.bottomCount) (cupWord form.cupBlock),
      cupWord_loops_zero form.cupBlock
        (processBrauer (brauerSeed form.bottomCount)
          (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle))
        conds3.fresh conds3.nfPos]
    exact hp3
  have hp5 : (processBrauer (brauerSeed form.bottomCount)
      (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
        ++ cupWord form.cupBlock ++ crossingWord form.topPerm)).loops = 0 := by
    rw [processBrauer_append
      (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
        ++ cupWord form.cupBlock) (brauerSeed form.bottomCount) (crossingWord form.topPerm),
      crossingWord_loops_zero form.topPerm
        (processBrauer (brauerSeed form.bottomCount)
          (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
            ++ cupWord form.cupBlock))
        conds4.fresh conds4.forest conds4.nfPos wfTop]
    exact hp4
  -- assemble: the boundary word + the circle block
  rw [hword, processBrauer_append
    (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
      ++ cupWord form.cupBlock ++ crossingWord form.topPerm) (brauerSeed form.bottomCount)
    (circleWord form.loops),
    circleFold_loops form.loops
      (processBrauer (brauerSeed form.bottomCount)
        (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
          ++ cupWord form.cupBlock ++ crossingWord form.topPerm))
      conds5.fresh conds5.forest conds5.nfPos,
    hp5, Nat.zero_add]

/-- ★★★ **THE LOOPS FIELD, general.**  For EVERY well-formed boundary involution `d` with `0 < d.bottomCount`, the
corrected six-phase fold reads back exactly `d.loops` closed circles: `foldLoopsField_ofForm` on the corrected form,
whose cap block is `natReplicate (capArcFeetIndices …).length 0` (`rfl`) and whose word is well-formed
(`wellFormedBrauerFold_correctedWord_general`).  This is the r29 loops wall, DISCHARGED for the `0 < bottomCount`
class — the sole open field of T-CLOSE(b). -/
theorem foldLoopsField_general (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    (processBrauer (brauerSeed d.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).loops = d.loops :=
  foldLoopsField_ofForm (reconstructStandardFormExt5Corrected d) bottomPos
    (capArcFeetIndices d.bottomCount d.partner).length rfl
    (wellFormedBrauerFold_correctedWord_general d wf)

/-! ## B2 — the loops field fired on the recon wild witnesses -/

/-- ★★ **The general loops field FIRES on the width-8 all-through wild diagram** (a genuine boundary involution). -/
theorem foldLoopsField_general_wildThrough :
    (processBrauer (brauerSeed wildThroughDiagram.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected wildThroughDiagram))).loops
      = wildThroughDiagram.loops :=
  foldLoopsField_general wildThroughDiagram (by decide) isBoundaryInvolution_wildThrough

/-- ★★ **The general loops field FIRES on the mixed through/cup/loop wild diagram** — two through strands, two top
cups, and TWO loops recovered by the general fold (not `decide`). -/
theorem foldLoopsField_general_wildCupLoop :
    (processBrauer (brauerSeed wildCupLoopDiagram.bottomCount)
        (standardFormWordExt5 (reconstructStandardFormExt5Corrected wildCupLoopDiagram))).loops
      = wildCupLoopDiagram.loops :=
  foldLoopsField_general wildCupLoopDiagram (by decide) isBoundaryInvolution_wildCupLoop

/-! ## B2 — the honesty marker -/

/-- ★★★ **Honesty marker — THE BOUNDARY CHAIN + THE LOOPS FIELD are SHIPPED (r31 B2).**  `crossingWord_loops_zero`
(D2), `cupWord_loops_zero` (D3), and `capWord_loops_zero_ofDistinct` (D4) close zero loops on the three boundary phase
words; `crossingWord_preserves_distinct` carries the seed distinctness through the bottom crossings into the cap phase;
`foldLoopsField_ofForm` welds them along the six-phase split (freshness threaded by
`brauerStateConditions_processBrauer`, the circle block by `circleFold_loops`), giving
`foldLoopsField_general`: for EVERY well-formed boundary involution with `0 < d.bottomCount`, the corrected fold's loop
count is exactly `d.loops`.  This DISCHARGES the r29 loops wall (`fxBrauer_hasFoldLoopsCorrectness`) — the sole open
field of T-CLOSE(b) — for the `0 < bottomCount` class, fired non-decidably on the wild witnesses
(`foldLoopsField_general_wildThrough` / `_wildCupLoop`).  The unconditional extraction close + the master flips are
B3/B4.  `= true`. -/
def fxBrauer_hasBoundaryWordLoopsField : Bool := true

end FX1Poly.Polygraph
