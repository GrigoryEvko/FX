import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutIdentityLayoutCollapse
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerMergeIntoHead
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallCountInvariance

/-! # Polygraph/TwoCategory/Amalgam/PushoutWhiskerLeftJunctionMerge — the PRODUCER-level junction-merge law
`firingBlockLayout_composePath` (the one new load-bearing piece), the frame-block SPLICE, its slot count, and the
whisker-of-identity route-agreement truth-probe (WP-AMALG-2 r21, Brick B1 — arm b)

r20 (`PushoutIdentityLayoutCollapse.lean`) shipped arm (a): the id-collapse canonical factorization.  r21 arm (b) is
the whiskerLeft JUNCTION MERGE: an `s`-carrying frame `oneCell` framing a body must open `wallCount(oneCell)` fresh
firing slots (its own `s`-walls) while the frame's trailing gap FUSES with the body's leading gap — the naive concat
`firingBlockLayout oneCell ++ bodyPairs` over-counts by one slot (two adjacent gaps, no wall between).  The r17 merge
arm `pushoutFactorizeWhiskerLeftMergeLayout` folds the WHOLE `oneCell` into ONE head wall (`n → n`), correct-canonical
only for a WALL-FREE frame; the junction merge decomposes the frame into its own firing blocks and splices with
junction fusion.

## The one new load-bearing piece — the PRODUCER merge law (this file, B1 core)

`firingBlockLayout_composePath oneCell path : firingBlockLayout (composePath oneCell path) = spliceFrameBlocks
(firingBlockLayout oneCell) path` — the PATH-granularity dual of the r10 width-level `finestGapWidthsAux_append`.
`spliceFrameBlocks frameBlocks path` splices `path`'s own producer run into the frame's LAST block (fusing the frame's
trailing gap with the body's leading gap) and keeps the frame's earlier blocks as fresh leading slots.  Proven by
STRUCTURAL induction on the frame path through the accumulator-general `firingBlockLayoutAux_composePath`: the frame's
`t`-gaps thread the widened accumulator, its `s`-walls cons one block and recurse, and the junction is the frame's
terminal `(pendingWall, currentGap)` accumulator handed off to `path` — exactly the producer's own mid-stream state.

The slot count follows: `(spliceFrameBlocks (firingBlockLayout oneCell) path).length = wallCount(oneCell) +
wallCount(path) + 1` (via the merge law + `firingBlockLayoutAux_length` + `pushoutPathWallCount_composePath`) — the
canonical spec count for `whiskerLeft oneCell body`, NOT the r17 `n`.

## The truth-probe FIRST (self-attack 2 — the whisker-of-identity route agreement)

`whiskerLeftJunctionMerge_producerRouteAgrees` checks, on a concrete `s·s`-frame over a `t·t` body, that the two
routes AGREE: (a) the producer directly on `composePath oneCell path`, and (b) the splice of the two producer runs.
This is the r8/r10 discipline: PROBE the merge law before the surgery.

## What STAYS WALLED (no flip)

This ships the PRODUCER merge law + the splice + its slot count + the route-agreement probe — the recon's one new
load-bearing piece.  The CONV-level whiskerLeft junction merge (`whiskerLeftFiringBlockMerge`) and its
`CanonicalFactorization` are the downstream deliverable; until BOTH arm b AND arm b' (whiskerRight dual) literally
ship, `fxAmalg_whiskerJunctionMergeStaysWalled` STAYS `true` and no master flips.  #2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL on the frame path; every reassociation propext-safe.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The frame-block SPLICE — splice a path's producer run into the frame's LAST block -/

/-- **The frame-block splice** — given the frame's firing-block list `frameBlocks` and a body `path`, splice `path`'s
own producer run into the frame's LAST block (whose accumulator is that block's `wall` / `gapDom`), keeping the earlier
frame blocks as fresh leading slots.  The frame's trailing gap FUSES with the body's leading gap — the junction merge.
Three non-overlapping arms (`[]` degenerate, `[block]` the last block = the junction, `block :: nextBlock :: rest` the
recursive prefix), structural on the list. -/
def spliceFrameBlocks :
    List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode) →
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode →
    List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)
  | [], _, _, path =>
      firingBlockLayoutAux (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) path
  | [block], _, _, path => firingBlockLayoutAux block.wall block.gapDom path
  | block :: nextBlock :: rest, _, _, path => block :: spliceFrameBlocks (nextBlock :: rest) path

/-- The splice of a `block :: nextBlock :: rest` prefix conses `block` and recurses (the third defining equation,
`rfl`) — the vehicle for pushing the splice past a cons whose tail is known to be a cons. -/
theorem spliceFrameBlocks_cons_cons
    (block nextBlock : VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)
    (rest : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode))
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) :
    spliceFrameBlocks (block :: nextBlock :: rest) path = block :: spliceFrameBlocks (nextBlock :: rest) path :=
  rfl

/-! ## The producer is never empty (the junction always exists) -/

/-- The coarse producer emits at least one block (the trailing gap) — `firingBlockLayoutAux pw cg path ≠ []`.  From
`firingBlockLayoutAux_length` (`= wallCount + 1 = succ _`): a `[]` output would have length `0 = succ _`, refuted by
`Nat.noConfusion`.  Lets the junction-splice push past the frame's LAST `s`-wall block (its tail is the always-cons
body run). -/
theorem firingBlockLayoutAux_ne_nil
    (pendingWall currentGap :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) :
    firingBlockLayoutAux pendingWall currentGap path ≠ [] :=
  fun hNil => Nat.noConfusion
    ((firingBlockLayoutAux_length pendingWall currentGap path).symm.trans (congrArg List.length hNil))

/-- Push the splice past a cons whose tail is a PRODUCER run (always a cons): `spliceFrameBlocks (block ::
firingBlockLayoutAux pw cg path') p = block :: spliceFrameBlocks (firingBlockLayoutAux pw cg path') p`.  Cases on the
producer run — the `[]` shape is refuted by `firingBlockLayoutAux_ne_nil`, the cons shape is the third splice equation.
-/
theorem spliceFrameBlocks_firingBlockCons
    (block : VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)
    (pendingWall currentGap :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    {frameSource frameTarget : Fin involutionMonadPushout.modeCount}
    (framePath : ModalityPath involutionMonadPushout.toModeGraph frameSource frameTarget)
    {bodySource bodyTarget : Fin involutionMonadPushout.modeCount}
    (bodyPath : ModalityPath involutionMonadPushout.toModeGraph bodySource bodyTarget) :
    spliceFrameBlocks (block :: firingBlockLayoutAux pendingWall currentGap framePath) bodyPath
      = block :: spliceFrameBlocks (firingBlockLayoutAux pendingWall currentGap framePath) bodyPath := by
  cases hRun : firingBlockLayoutAux pendingWall currentGap framePath with
  | nil => exact absurd hRun (firingBlockLayoutAux_ne_nil pendingWall currentGap framePath)
  | cons headBlock tailBlocks => rfl

/-! ## THE PRODUCER MERGE LAW (accumulator-general, structural on the frame) -/

/-- ★★★ **THE PRODUCER MERGE LAW (accumulator form).**  `firingBlockLayoutAux pendingWall currentGap (composePath
frame path) = spliceFrameBlocks (firingBlockLayoutAux pendingWall currentGap frame) path` — reading the fused path
`composePath frame path` is reading the frame (emitting its `s`-wall blocks, threading its `t`-gaps) then handing the
frame's TERMINAL accumulator to the body run, which is exactly splicing the body's producer run into the frame's last
block.  STRUCTURAL on the frame path: `.nil` hands `(pendingWall, currentGap)` straight to the body (the sole frame
block IS the junction, `rfl`); the `t`-gap (`false`) case threads the IH with the widened accumulator; the `s`-wall
(`true`) case conses the closed block and pushes the splice past it via `spliceFrameBlocks_firingBlockCons`. -/
theorem firingBlockLayoutAux_composePath
    (pendingWall currentGap :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    {frameSource frameMiddle bodyTarget : Fin involutionMonadPushout.modeCount} →
    (frame : ModalityPath involutionMonadPushout.toModeGraph frameSource frameMiddle) →
    (path : ModalityPath involutionMonadPushout.toModeGraph frameMiddle bodyTarget) →
    firingBlockLayoutAux pendingWall currentGap (composePath frame path)
      = spliceFrameBlocks (firingBlockLayoutAux pendingWall currentGap frame) path
  | _, _, _, .nil _, path => rfl
  | _, _, _, .cons letter rest, path => by
      show (bif letterTag involutionMonadSplit letter.val then
              idBlockPair pendingWall currentGap ::
                firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
                  (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
                  (composePath rest path)
            else
              firingBlockLayoutAux pendingWall
                (composePath currentGap (pushoutEndoPathOfWord [letter.val])) (composePath rest path))
          = spliceFrameBlocks (bif letterTag involutionMonadSplit letter.val then
              idBlockPair pendingWall currentGap ::
                firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
                  (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest
            else
              firingBlockLayoutAux pendingWall
                (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest) path
      cases hTag : letterTag involutionMonadSplit letter.val with
      | false =>
          show firingBlockLayoutAux pendingWall
                (composePath currentGap (pushoutEndoPathOfWord [letter.val])) (composePath rest path)
              = spliceFrameBlocks (firingBlockLayoutAux pendingWall
                  (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest) path
          exact firingBlockLayoutAux_composePath pendingWall
            (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest path
      | true =>
          show idBlockPair pendingWall currentGap ::
                firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
                  (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
                  (composePath rest path)
              = spliceFrameBlocks (idBlockPair pendingWall currentGap ::
                  firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
                    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest) path
          rw [spliceFrameBlocks_firingBlockCons (idBlockPair pendingWall currentGap)
                (pushoutEndoPathOfWord [letter.val])
                (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest path,
              firingBlockLayoutAux_composePath (pushoutEndoPathOfWord [letter.val])
                (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest path]

/-- ★★★ **THE PRODUCER MERGE LAW (`firingBlockLayout` form).**  `firingBlockLayout (composePath oneCell path) =
spliceFrameBlocks (firingBlockLayout oneCell) path` — the coarse producer on a composed 1-cell splices the body's run
into the frame's last block.  The accumulator-general law at the empty starting accumulators; the WP-AMALG-3
inheritance producer piece. -/
theorem firingBlockLayout_composePath
    (oneCell : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    {bodyTarget : Fin involutionMonadPushout.modeCount}
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode bodyTarget) :
    firingBlockLayout (composePath oneCell path)
      = spliceFrameBlocks (firingBlockLayout oneCell) path :=
  firingBlockLayoutAux_composePath
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) oneCell path

/-! ## The splice slot count — the CANONICAL count for `whiskerLeft oneCell body` -/

/-- ★★★ **THE JUNCTION SPLICE SLOT COUNT.**  `(spliceFrameBlocks (firingBlockLayout oneCell) path).length =
wallCount(oneCell) + wallCount(path) + 1` — the frame opens `wallCount(oneCell)` fresh slots, the body opens
`wallCount(path)` more, and the fused junction gap is the single trailing `+ 1`.  This is the CANONICAL spec count for
`whiskerLeft oneCell body` (its domain is `composePath oneCell (dom body)`), NOT the r17 merge arm's `n`.  Via the
merge law + `firingBlockLayoutAux_length` + `pushoutPathWallCount_composePath`. -/
theorem spliceFrameBlocks_firingBlockLayout_slotCount
    (oneCell path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    (spliceFrameBlocks (firingBlockLayout oneCell) path).length
      = pushoutPathWallCount oneCell + pushoutPathWallCount path + 1 := by
  rw [← firingBlockLayout_composePath oneCell path, firingBlockLayout,
      firingBlockLayoutAux_length, pushoutPathWallCount_composePath]

/-! ## The truth-probe — the whisker-of-identity route agreement (FIRST) -/

/-- ★★★ **TRUTH-PROBE (self-attack 2 — the producer routes AGREE).**  On a concrete `s·s`-frame over a `t·t` body,
the two routes coincide: the producer directly on the fused 1-cell `composePath (s·s) (t·t)`, and the splice of the two
separate producer runs.  `firingBlockLayout_composePath` on the very cells the r8 wall-splitter and the all-gap
degenerate case use — the merge law probed before the surgery. -/
theorem whiskerLeftJunctionMerge_producerRouteAgrees :
    firingBlockLayout (composePath unitSplitsWallDom (composePath monadPushTPath monadPushTPath))
      = spliceFrameBlocks (firingBlockLayout unitSplitsWallDom)
          (composePath monadPushTPath monadPushTPath) :=
  firingBlockLayout_composePath unitSplitsWallDom (composePath monadPushTPath monadPushTPath)

/-- ★★★ **PROBE (junction slot count on the `s·s`/`t·t` frame) — THREE slots.**  `(spliceFrameBlocks (firingBlockLayout
(s·s)) (t·t)).length = 3` (`rfl`): the two `s`-walls of the frame open two fresh slots, the `t·t` body run fuses into
the frame's trailing junction (one slot), total `wallCount(s·s) + wallCount(t·t) + 1 = 2 + 0 + 1 = 3` — the canonical
count, matching the direct producer on `s·s·t·t`. -/
theorem whiskerLeftJunctionMerge_sliceSlotCount :
    (spliceFrameBlocks (firingBlockLayout unitSplitsWallDom)
      (composePath monadPushTPath monadPushTPath)).length = 3 := rfl

/-- ★★★ **PROBE (junction slot count on the `s·s`/`s·s` frame) — FIVE slots.**  `(spliceFrameBlocks (firingBlockLayout
(s·s)) (s·s)).length = 5` (`rfl`): a wall-heavy frame AND a wall-heavy body, `wallCount(s·s) + wallCount(s·s) + 1 = 2 +
2 + 1 = 5` — the junction merge counts BOTH frames' walls, contrast the r17 merge arm's `3` (the body count, the whole
frame buried in one head wall). -/
theorem whiskerLeftJunctionMerge_sliceSlotCountWallHeavy :
    (spliceFrameBlocks (firingBlockLayout unitSplitsWallDom) unitSplitsWallDom).length = 5 := rfl

/-! ## Observability -/

-- The junction splice slot counts: `s·s`-frame over `t·t` (expect `3`), over `s·s` (expect `5`).
#eval (spliceFrameBlocks (firingBlockLayout unitSplitsWallDom)
        (composePath monadPushTPath monadPushTPath)).length
#eval (spliceFrameBlocks (firingBlockLayout unitSplitsWallDom) unitSplitsWallDom).length

/-! ## Honesty marker (the producer merge law only — the CONV arm is the downstream deliverable) -/

/-- ★★★ **Honesty marker — the PRODUCER-level junction merge law SHIPS (WP-AMALG-2 r21, B1 core).**  `= true`.
`firingBlockLayout_composePath` (the recon's one new load-bearing piece, the PATH-granularity dual of the r10
width-level `finestGapWidthsAux_append`): `firingBlockLayout (composePath oneCell path) = spliceFrameBlocks
(firingBlockLayout oneCell) path`, proven STRUCTURALLY on the frame through the accumulator-general
`firingBlockLayoutAux_composePath` (the `.nil` junction hand-off `rfl`, the `t`-gap widened-accumulator IH, the
`s`-wall cons pushed past by `spliceFrameBlocks_firingBlockCons` + `firingBlockLayoutAux_ne_nil`).  The splice slot
count is the CANONICAL count `wallCount(oneCell) + wallCount(path) + 1` (`spliceFrameBlocks_firingBlockLayout_slotCount`),
NOT the r17 merge arm's `n`.  The routes AGREE on the concrete `s·s`/`t·t` frame
(`whiskerLeftJunctionMerge_producerRouteAgrees`), the junction slot counts probe `3` and `5`.

This ships the PRODUCER merge law + splice + slot count + route-agreement probe — the load-bearing piece the CONV-level
whiskerLeft junction merge and its `CanonicalFactorization` consume.  It does NOT by itself flip
`fxAmalg_whiskerJunctionMergeStaysWalled` (that flips only when BOTH the whiskerLeft AND whiskerRight CONV-level
junction canonical factorizations literally ship).  #2043 does NOT close.  `= true`. -/
def fxAmalg_hasFiringBlockProducerMergeLaw : Bool := true

end FX1Poly.Polygraph.Amalgam
