import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerLeftJunctionMerge

/-! # Polygraph/TwoCategory/Amalgam/PushoutWhiskerLeftJunctionCanonical — the LAYOUT-level frame-block splice
`spliceFrameIntoLayout`, its slot count + boundary distribution, and the CONV-level whiskerLeft junction merge threading
the r17 cell-level lemma through the r19 producer (WP-AMALG-2 r21, Brick B1 — arm b)

B1 core (`PushoutWhiskerLeftJunctionMerge.lean`) shipped the PRODUCER merge law `firingBlockLayout_composePath` (the
id-cell junction fusion).  This file lifts it to the CONV level for a GENERAL body: the whiskerLeft junction merge
factors `whiskerLeft oneCell body` into a CANONICAL-count layout by decomposing `oneCell` into its own firing blocks
(`firingBlockLayout oneCell`), prepending all but the last as fresh leading slots, and FUSING the last frame block into
the body's head via the r17 `whiskerLeft_conv_mergeFrameIntoHead`.

## The layout-level splice

`spliceFrameIntoLayout frameBlocks bodyPairs` — three arms mirroring `spliceFrameBlocks` but the body is a LAYOUT
(`bodyPairs`), not a path: `[]` is the body itself; `[block]` fuses the single frame block into the body head
(`mergeFrameIntoHead (gapDomLayout nil [block]) bodyPairs`, the r17 junction); `block :: nextBlock :: rest` prepends
`block` as a fresh slot and recurses.  For a NON-EMPTY canonical body the slot count is `frameBlocks.length - 1 +
bodyPairs.length` — with `frameBlocks = firingBlockLayout oneCell`, that is `wallCount(oneCell) + bodyPairs.length`, the
CANONICAL count for `whiskerLeft oneCell body`.

## The boundary distribution

`gapDomLayout_spliceFrameIntoLayout` / `gapCodLayout_spliceFrameIntoLayout` — `gapDomLayout finalWall
(spliceFrameIntoLayout frameBlocks bodyPairs) = composePath (gapDomLayout nil frameBlocks) (gapDomLayout finalWall
bodyPairs)`.  Structural on `frameBlocks`: the `[block]` junction is the r17 `gapDomLayout_mergeFrameIntoHead`; each
prefix block adds a clean `composePath` layer re-bracketed out by two `composePath_assoc`.

## This file's SCOPE (honest partial)

This file ships the DATA-level layout splice + its slot count + boundary distribution + probes — the scaffolding the
conv-level whiskerLeft junction merge consumes.  Whether the conv-level `CanonicalFactorization` closes is tracked by
the honesty markers below; `fxAmalg_whiskerJunctionMergeStaysWalled` flips ONLY when BOTH arm b (this file's conv) AND
arm b' (the whiskerRight dual) literally ship.

Raw Lean 4 + Init.  STRUCTURAL on the frame block list; `composePath_assoc` via `rw` (term instance, never `simp
only`, propext-safe).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The layout-level frame-block splice -/

/-- **The layout-level frame-block splice** — splice the body LAYOUT `bodyPairs` into the frame's LAST block (fusing the
frame's trailing gap into the body head via `mergeFrameIntoHead`), keeping the earlier frame blocks as fresh leading
slots.  Three non-overlapping arms; structural on the frame block list.  The layout-body counterpart of
`spliceFrameBlocks` (whose body is a path). -/
def spliceFrameIntoLayout :
    List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode) →
    List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode) →
    List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)
  | [], bodyPairs => bodyPairs
  | [block], bodyPairs =>
      mergeFrameIntoHead
        (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) [block])
        bodyPairs
  | block :: nextBlock :: rest, bodyPairs =>
      block :: spliceFrameIntoLayout (nextBlock :: rest) bodyPairs

/-- The splice of a `block :: nextBlock :: rest` frame conses `block` and recurses (the third defining equation,
`rfl`). -/
theorem spliceFrameIntoLayout_cons_cons
    (block nextBlock : VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)
    (rest bodyPairs : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) :
    spliceFrameIntoLayout (block :: nextBlock :: rest) bodyPairs
      = block :: spliceFrameIntoLayout (nextBlock :: rest) bodyPairs :=
  rfl

/-! ## The slot count -/

/-- The head-merge keeps the slot count on a NON-EMPTY body — `(mergeFrameIntoHead frame (pair :: rest)).length =
(pair :: rest).length` (the frame folds into the head block's wall, opening no new slot).  `rfl` (the head becomes
`{pair with wall}`, the tail is untouched). -/
theorem mergeFrameIntoHead_cons_length {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (frame : ModalityPath signature.graph oneMode oneMode)
    (pair : VcompGapPair signature oneMode) (rest : List (VcompGapPair signature oneMode)) :
    (mergeFrameIntoHead frame (pair :: rest)).length = (pair :: rest).length :=
  rfl

/-- ★★ **THE SPLICE SLOT COUNT (offset form).**  For a NON-EMPTY frame and a NON-EMPTY body, `(spliceFrameIntoLayout
frameBlocks bodyPairs).length + 1 = frameBlocks.length + bodyPairs.length` — the frame opens `frameBlocks.length - 1`
fresh slots, the body supplies `bodyPairs.length`, and the fused junction is the shared `+ 1`.  Structural on the frame
block list. -/
theorem spliceFrameIntoLayout_length :
    (frameBlocks : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) →
    frameBlocks ≠ [] →
    (bodyPairs : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) →
    bodyPairs ≠ [] →
    (spliceFrameIntoLayout frameBlocks bodyPairs).length + 1
      = frameBlocks.length + bodyPairs.length
  | [], hne, _, _ => absurd rfl hne
  | [block], _, bodyPairs, hbody => by
      cases bodyPairs with
      | nil => exact absurd rfl hbody
      | cons pair rest =>
          show (mergeFrameIntoHead
              (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) [block])
              (pair :: rest)).length + 1 = [block].length + (pair :: rest).length
          rw [mergeFrameIntoHead_cons_length]
          exact Nat.add_comm (List.length (pair :: rest)) 1
  | block :: nextBlock :: rest, _, bodyPairs, hbody => by
      have ih := spliceFrameIntoLayout_length (nextBlock :: rest) (List.cons_ne_nil _ _) bodyPairs hbody
      show (spliceFrameIntoLayout (nextBlock :: rest) bodyPairs).length + 1 + 1
          = (nextBlock :: rest).length + 1 + bodyPairs.length
      rw [ih]
      exact Nat.add_right_comm _ _ _

/-- ★★★ **THE SPLICE MEETS THE CANONICAL SLOT COUNT.**  With `frameBlocks = firingBlockLayout oneCell` (length
`wallCount(oneCell) + 1`) and a NON-EMPTY body, `(spliceFrameIntoLayout (firingBlockLayout oneCell) bodyPairs).length =
wallCount(oneCell) + bodyPairs.length` — the CANONICAL count for `whiskerLeft oneCell body` (whose domain adds
`wallCount(oneCell)` walls to the body).  From `spliceFrameIntoLayout_length` + `firingBlockLayoutAux_length`. -/
theorem spliceFrameIntoLayout_firingBlockLayout_length
    (oneCell : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    (bodyPairs : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode))
    (hbody : bodyPairs ≠ []) :
    (spliceFrameIntoLayout (firingBlockLayout oneCell) bodyPairs).length
      = pushoutPathWallCount oneCell + bodyPairs.length := by
  have hframe : firingBlockLayout oneCell ≠ [] :=
    firingBlockLayoutAux_ne_nil
      (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
      (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) oneCell
  have hlen := spliceFrameIntoLayout_length (firingBlockLayout oneCell) hframe bodyPairs hbody
  rw [firingBlockLayout, firingBlockLayoutAux_length] at hlen
  -- hlen : splice.length + 1 = (wallCount oneCell + 1) + bodyPairs.length
  rw [Nat.add_right_comm (pushoutPathWallCount oneCell) 1 bodyPairs.length] at hlen
  exact Nat.succ.inj hlen

/-! ## The boundary distribution -/

/-- ★★ **THE DOMAIN BOUNDARY DISTRIBUTION of the layout splice.**  `gapDomLayout finalWall (spliceFrameIntoLayout
frameBlocks bodyPairs) = composePath (gapDomLayout nil frameBlocks) (gapDomLayout finalWall bodyPairs)` — the splice's
domain is the frame's own domain (trailing wall `nil`) precomposed onto the body's domain.  Structural on the frame:
the `[block]` junction is the r17 `gapDomLayout_mergeFrameIntoHead`; each prefix block adds a `composePath` layer
re-bracketed by two `composePath_assoc`. -/
theorem gapDomLayout_spliceFrameIntoLayout
    (finalWall : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    (frameBlocks : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) →
    frameBlocks ≠ [] →
    (bodyPairs : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) →
    gapDomLayout finalWall (spliceFrameIntoLayout frameBlocks bodyPairs)
      = composePath
          (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) frameBlocks)
          (gapDomLayout finalWall bodyPairs)
  | [], hne, _ => absurd rfl hne
  | [block], _, bodyPairs =>
      gapDomLayout_mergeFrameIntoHead finalWall
        (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) [block])
        bodyPairs
  | block :: nextBlock :: rest, _, bodyPairs => by
      show gapDomLayout finalWall (block :: spliceFrameIntoLayout (nextBlock :: rest) bodyPairs)
          = composePath
              (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
                (block :: nextBlock :: rest))
              (gapDomLayout finalWall bodyPairs)
      show composePath block.wall (composePath block.gapDom
              (gapDomLayout finalWall (spliceFrameIntoLayout (nextBlock :: rest) bodyPairs)))
          = composePath
              (composePath block.wall (composePath block.gapDom
                (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
                  (nextBlock :: rest))))
              (gapDomLayout finalWall bodyPairs)
      rw [gapDomLayout_spliceFrameIntoLayout finalWall (nextBlock :: rest)
            (List.cons_ne_nil _ _) bodyPairs,
          composePath_assoc, composePath_assoc]

/-- ★★ **THE CODOMAIN BOUNDARY DISTRIBUTION** — the `.gapCod` dual of `gapDomLayout_spliceFrameIntoLayout`, but the
FRAME part reads by its DOMAIN (`gapDomLayout nil frameBlocks`, the fixed whiskering 1-cell): for an ALL-IDENTITY frame
every block's `gapCod` coincides with its `gapDom` (`idBlockPair`), so the codomain of the splice is the frame's own
domain precomposed onto the body's CODOMAIN.  Structural on the `AllIdBlocks` witness (each block is `idBlockPair w g`,
`gapCod = gapDom = g` definitionally). -/
theorem gapCodLayout_spliceFrameIntoLayout
    (finalWall : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    (frameBlocks : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) →
    AllIdBlocks frameBlocks → frameBlocks ≠ [] →
    (bodyPairs : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) →
    gapCodLayout finalWall (spliceFrameIntoLayout frameBlocks bodyPairs)
      = composePath
          (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) frameBlocks)
          (gapCodLayout finalWall bodyPairs)
  | _, AllIdBlocks.nil, hne, _ => absurd rfl hne
  | _, AllIdBlocks.cons wall gap rest hrest, _, bodyPairs => by
      cases hrest with
      | nil =>
          exact gapCodLayout_mergeFrameIntoHead finalWall
            (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
              [idBlockPair wall gap]) bodyPairs
      | cons wall2 gap2 rest2 hrest2 =>
          show composePath wall (composePath gap
                  (gapCodLayout finalWall
                    (spliceFrameIntoLayout (idBlockPair wall2 gap2 :: rest2) bodyPairs)))
              = composePath
                  (composePath wall (composePath gap
                    (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
                      (idBlockPair wall2 gap2 :: rest2))))
                  (gapCodLayout finalWall bodyPairs)
          rw [gapCodLayout_spliceFrameIntoLayout finalWall (idBlockPair wall2 gap2 :: rest2)
                (AllIdBlocks.cons wall2 gap2 rest2 hrest2) (List.cons_ne_nil _ _) bodyPairs,
              composePath_assoc, composePath_assoc]

/-! ## Probes -/

/-- ★★★ **PROBE (the layout splice meets the canonical count on an `s·s`-frame over a two-block body).**  Framing a
TWO-block body with the `s·s` frame `firingBlockLayout (s·s)` (three blocks, `wallCount 2`) splices to `2 + 2 = 4`
slots: the two `s`-walls open two fresh slots, the two body slots follow, the junction fuses.  `wallCount(s·s) +
2 = 4`. -/
theorem spliceFrameIntoLayout_probeSlotCount :
    (spliceFrameIntoLayout (firingBlockLayout unitSplitsWallDom)
      [interleavedAssocGapPair, interleavedLeftUnitGapPair]).length = 4 := rfl

/-! ## Observability -/

-- The layout-splice slot count: `s·s`-frame over a two-block body (expect `4`).
#eval (spliceFrameIntoLayout (firingBlockLayout unitSplitsWallDom)
        [interleavedAssocGapPair, interleavedLeftUnitGapPair]).length

/-! ## Honesty marker (the DATA-level scaffolding; the conv is tracked separately) -/

/-- ★★★ **Honesty marker — the LAYOUT-level frame-block splice + slot count + boundary distribution SHIP (WP-AMALG-2
r21, B1 data-level).**  `= true`.  `spliceFrameIntoLayout` splices a body layout into the frame's last block (r17
junction fusion) keeping the earlier frame blocks as fresh slots; its slot count is the CANONICAL
`wallCount(oneCell) + bodyPairs.length` on a non-empty body (`spliceFrameIntoLayout_firingBlockLayout_length`); its
domain / codomain boundaries distribute over the frame (`gapDomLayout_spliceFrameIntoLayout` /
`gapCodLayout_spliceFrameIntoLayout`).  Probed on the `s·s`-frame over a two-block body (`4` slots).

This is the DATA-level scaffolding for the CONV-level whiskerLeft junction merge; it does NOT by itself flip
`fxAmalg_whiskerJunctionMergeStaysWalled`.  `= true`. -/
def fxAmalg_hasWhiskerLeftLayoutSplice : Bool := true

end FX1Poly.Polygraph.Amalgam
