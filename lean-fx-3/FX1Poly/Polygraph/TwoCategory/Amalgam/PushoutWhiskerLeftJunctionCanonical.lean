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

/-! ## THE CONV-LEVEL whiskerLeft JUNCTION MERGE (threading r17 through the r19 producer) -/

/-- ★★★ **THE CONV-LEVEL whiskerLeft JUNCTION MERGE.**  For an ALL-IDENTITY frame block list, `whiskerLeft
(gapDomLayout nil frameBlocks) (gapVcompLayout finalWall bodyPairs)` is saturated-convertible to the layout splice
`gapVcompLayout finalWall (spliceFrameIntoLayout frameBlocks bodyPairs)` (up to the boundary-distribution cast) — the
frame's `s`-walls open fresh leading slots and its trailing gap FUSES into the body head.

Structural on the `AllIdBlocks` witness.  The SINGLE-block case is the r17 cell-level merge
`whiskerLeft_conv_mergeFrameIntoHead` (the whole one-block frame folds into the head — the junction).  The cons case
PEELS the head frame block by `whiskerLeftComp` (twice: `composePath wall (composePath gap ·)`), threads the IH on the
frame tail, pushes the IH cast out (`whiskerLeftCastBoundaryEq`), unfolds the peeled `gap`-whisker to
`hcomp (vcomp (id gap) (id gap)) ·` (`whiskerLeft_conv_hcompIdLeading` + `vcompIdLeft`), and re-folds the leading
`wall`-whisker (`whiskerLeft_conv_hcompIdLeading`) into `hcomp (id wall) ·` — exactly the head block
`idBlockPair wall gap`.  The per-block associator casts merge into the single boundary-distribution cast by
`castBoundary_trans` + `Eq` proof irrelevance. -/
theorem whiskerLeftFiringBlockMerge
    (finalWall : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    (frameBlocks : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) →
    (allId : AllIdBlocks frameBlocks) → (hne : frameBlocks ≠ []) →
    (bodyPairs : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) →
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (RawTwoCellExpr.whiskerLeft
        (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) frameBlocks)
        (gapVcompLayout finalWall bodyPairs))
      (RawTwoCellExpr.castBoundary
        (gapDomLayout_spliceFrameIntoLayout finalWall frameBlocks hne bodyPairs)
        (gapCodLayout_spliceFrameIntoLayout finalWall frameBlocks allId hne bodyPairs)
        (gapVcompLayout finalWall (spliceFrameIntoLayout frameBlocks bodyPairs)))
  | _, AllIdBlocks.nil, hne, _ => absurd rfl hne
  | _, AllIdBlocks.cons wall gap rest hrest, _, bodyPairs => by
    cases hrest with
    | nil =>
        exact whiskerLeft_conv_mergeFrameIntoHead finalWall
          (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
            [idBlockPair wall gap]) bodyPairs
    | cons wall2 gap2 tailFrame2 hrest2 =>
      have ih := whiskerLeftFiringBlockMerge finalWall (idBlockPair wall2 gap2 :: tailFrame2)
        (AllIdBlocks.cons wall2 gap2 tailFrame2 hrest2) (List.cons_ne_nil _ _) bodyPairs
      have gapToZ := SaturatedConvOver.trans
        (whiskerLeft_conv_hcompIdLeading (baseRel := crossPairRealPushoutRel) gap
          (gapVcompLayout finalWall (spliceFrameIntoLayout (idBlockPair wall2 gap2 :: tailFrame2) bodyPairs)))
        (SaturatedConvOver.symm (SaturatedConvOver.hcompCongrLeft
          (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id gap))))
          (gapVcompLayout finalWall (spliceFrameIntoLayout (idBlockPair wall2 gap2 :: tailFrame2) bodyPairs))))
      have innerStep := SaturatedConvOver.whiskerLeftCongr gap ih
      rw [whiskerLeftCastBoundaryEq] at innerStep
      have innerG := SaturatedConvOver.trans innerStep
        (SaturatedConvOver.castBoundaryCongr _ _ gapToZ)
      have midStep := SaturatedConvOver.trans
        (SaturatedConvOver.ofFull (TwoCellConvFull.whiskerLeftComp gap
          (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
            (idBlockPair wall2 gap2 :: tailFrame2)) (gapVcompLayout finalWall bodyPairs)))
        (SaturatedConvOver.castBoundaryCongr _ _ innerG)
      rw [RawTwoCellExpr.castBoundary_trans] at midStep
      have outerStep := SaturatedConvOver.whiskerLeftCongr wall midStep
      rw [whiskerLeftCastBoundaryEq] at outerStep
      have outerG := SaturatedConvOver.trans outerStep
        (SaturatedConvOver.castBoundaryCongr _ _
          (whiskerLeft_conv_hcompIdLeading wall
            (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp (RawTwoCellExpr.id gap) (RawTwoCellExpr.id gap))
              (gapVcompLayout finalWall (spliceFrameIntoLayout (idBlockPair wall2 gap2 :: tailFrame2) bodyPairs)))))
      have result := SaturatedConvOver.trans
        (SaturatedConvOver.ofFull (TwoCellConvFull.whiskerLeftComp wall
          (composePath gap
            (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
              (idBlockPair wall2 gap2 :: tailFrame2)))
          (gapVcompLayout finalWall bodyPairs)))
        (SaturatedConvOver.castBoundaryCongr _ _ outerG)
      rw [RawTwoCellExpr.castBoundary_trans] at result
      exact result

/-- ★★ **THE whiskerLeft JUNCTION MERGE at a NAMED frame 1-cell.**  The frame of `whiskerLeftFiringBlockMerge` is
intrinsically `gapDomLayout nil frameBlocks`; this wrapper re-states it at ANY frame `frameCell` propositionally equal
to that layout (the r19 round-trip `oneCell = gapDomLayout nil (firingBlockLayout oneCell)`), the boundary casts
supplied at `frameCell`.  `subst` on the frame equality (`frameCell` and `frameBlocks` are independent here — no
circularity) reduces it to `whiskerLeftFiringBlockMerge`; the caller's casts reconcile by proof irrelevance. -/
theorem whiskerLeftFiringBlockMergeAtFrame
    (finalWall frameCell : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    (frameBlocks : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode))
    (allId : AllIdBlocks frameBlocks) (hne : frameBlocks ≠ [])
    (bodyPairs : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode))
    (hframe : frameCell
      = gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) frameBlocks)
    (hDom : gapDomLayout finalWall (spliceFrameIntoLayout frameBlocks bodyPairs)
      = composePath frameCell (gapDomLayout finalWall bodyPairs))
    (hCod : gapCodLayout finalWall (spliceFrameIntoLayout frameBlocks bodyPairs)
      = composePath frameCell (gapCodLayout finalWall bodyPairs)) :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (RawTwoCellExpr.whiskerLeft frameCell (gapVcompLayout finalWall bodyPairs))
      (RawTwoCellExpr.castBoundary hDom hCod
        (gapVcompLayout finalWall (spliceFrameIntoLayout frameBlocks bodyPairs))) := by
  subst hframe
  exact whiskerLeftFiringBlockMerge finalWall frameBlocks allId hne bodyPairs

/-! ## THE whiskerLeft JUNCTION CANONICAL FACTORIZATION (arm b) -/

/-- ★★★ **THE whiskerLeft JUNCTION CANONICAL FACTORIZATION (arm b, the recon deliverable).**  Given a
`CanonicalFactorization` of `body`, `whiskerLeft oneCell body` has a `CanonicalFactorization` whose `pairs` are the
layout splice `spliceFrameIntoLayout (firingBlockLayout oneCell) bodyFact.pairs` — the frame's own firing blocks
spliced into the body, junction fused.  The slot count is the CANONICAL `wallCount(oneCell) + bodyFact.pairs.length =
wallCount(composePath oneCell (dom body)) + 1` (via `spliceFrameIntoLayout_firingBlockLayout_length` + the body's slot
spec + `pushoutPathWallCount_composePath`), the boundary equalities are the splice distributions re-anchored by the r19
round-trip `gapDomLayout_firingBlockLayout`, and the convertibility threads `bodyFact.conv` under `whiskerLeftCongr`
then `whiskerLeftFiringBlockMerge`, the per-side casts reconciled by `castBoundary_trans` + `Eq` proof irrelevance. -/
def whiskerLeftJunctionCanonical
    (oneCell : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {body : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath}
    (bodyFact : CanonicalFactorization body) :
    CanonicalFactorization (RawTwoCellExpr.whiskerLeft oneCell body) := by
  have hpairs : bodyFact.1.pairs ≠ [] := by
    intro hnil
    have hzero := bodyFact.2.symm.trans (congrArg List.length hnil)
    rw [finestGapWidths_pushoutPathTags_length] at hzero
    exact Nat.noConfusion hzero
  refine ⟨{ finalWall := bodyFact.1.finalWall
            pairs := spliceFrameIntoLayout (firingBlockLayout oneCell) bodyFact.1.pairs
            domEq := ?_
            codEq := ?_
            conv := ?_ }, ?_⟩
  · rw [gapDomLayout_spliceFrameIntoLayout _ (firingBlockLayout oneCell)
        (firingBlockLayoutAux_ne_nil _ _ oneCell) bodyFact.1.pairs,
        gapDomLayout_firingBlockLayout, ← bodyFact.1.domEq]
  · rw [gapCodLayout_spliceFrameIntoLayout _ (firingBlockLayout oneCell)
        (firingBlockLayoutAux_allIdBlocks _ _ oneCell)
        (firingBlockLayoutAux_ne_nil _ _ oneCell) bodyFact.1.pairs,
        gapDomLayout_firingBlockLayout, ← bodyFact.1.codEq]
  · have junctionDom : gapDomLayout bodyFact.1.finalWall
        (spliceFrameIntoLayout (firingBlockLayout oneCell) bodyFact.1.pairs)
        = composePath oneCell (gapDomLayout bodyFact.1.finalWall bodyFact.1.pairs) :=
      (gapDomLayout_spliceFrameIntoLayout bodyFact.1.finalWall (firingBlockLayout oneCell)
        (firingBlockLayoutAux_ne_nil _ _ oneCell) bodyFact.1.pairs).trans
        (congrArg (fun frameDom => composePath frameDom (gapDomLayout bodyFact.1.finalWall bodyFact.1.pairs))
          (gapDomLayout_firingBlockLayout oneCell))
    have junctionCod : gapCodLayout bodyFact.1.finalWall
        (spliceFrameIntoLayout (firingBlockLayout oneCell) bodyFact.1.pairs)
        = composePath oneCell (gapCodLayout bodyFact.1.finalWall bodyFact.1.pairs) :=
      (gapCodLayout_spliceFrameIntoLayout bodyFact.1.finalWall (firingBlockLayout oneCell)
        (firingBlockLayoutAux_allIdBlocks _ _ oneCell) (firingBlockLayoutAux_ne_nil _ _ oneCell)
        bodyFact.1.pairs).trans
        (congrArg (fun frameDom => composePath frameDom (gapCodLayout bodyFact.1.finalWall bodyFact.1.pairs))
          (gapDomLayout_firingBlockLayout oneCell))
    have merge := whiskerLeftFiringBlockMergeAtFrame bodyFact.1.finalWall oneCell (firingBlockLayout oneCell)
      (firingBlockLayoutAux_allIdBlocks _ _ oneCell) (firingBlockLayoutAux_ne_nil _ _ oneCell) bodyFact.1.pairs
      (gapDomLayout_firingBlockLayout oneCell).symm junctionDom junctionCod
    have chain := SaturatedConvOver.trans (SaturatedConvOver.whiskerLeftCongr oneCell bodyFact.1.conv) merge
    rw [whiskerLeftCastBoundaryEq] at chain
    have reconciled := SaturatedConvOver.castBoundaryCongr junctionDom.symm junctionCod.symm chain
    rw [RawTwoCellExpr.castBoundary_trans, RawTwoCellExpr.castBoundary_trans] at reconciled
    exact reconciled
  · have rhs : (finestGapWidths (pushoutPathTags (composePath oneCell sourcePath))).length
        = pushoutPathWallCount oneCell + (pushoutPathWallCount sourcePath + 1) := by
      rw [finestGapWidths_pushoutPathTags_length, pushoutPathWallCount_composePath, Nat.add_assoc]
    exact (spliceFrameIntoLayout_firingBlockLayout_length oneCell bodyFact.1.pairs hpairs).trans
      ((congrArg (pushoutPathWallCount oneCell + ·)
        (bodyFact.2.trans (finestGapWidths_pushoutPathTags_length sourcePath))).trans rhs.symm)

/-! ## Witness + probe (a wall-frame over the wire-changing `mu`) -/

/-- ★★★ **THE whiskerLeft JUNCTION WITNESS — an `s`-wall frame over the wire-changing `mu`.**  `whiskerLeft s
(gen mu)` (`gen mu : t·t ⇒ t`, framed by the `s`-wall) factors CANONICALLY via `whiskerLeftJunctionCanonical` on the
`gen` arm `mulCanonicalFactorization` — the `s`-wall opens ONE fresh leading slot, the `mu` firing sits in the fused
junction gap UNTOUCHED.  A non-vacuous inhabitant at the REAL pushout signature, over a WIRE-CHANGING body. -/
def whiskerLeftJunctionMuWitness :
    CanonicalFactorization (RawTwoCellExpr.whiskerLeft monadPushSPath (RawTwoCellExpr.gen pushoutMonadMult)) :=
  whiskerLeftJunctionCanonical monadPushSPath mulCanonicalFactorization

/-- ★★★ **PROBE (junction witness slot count — TWO slots, the canonical count).**  `whiskerLeftJunctionMuWitness.1.
pairs.length = 2` (`rfl`): the `s`-wall opens one fresh slot, the `mu` junction gap is the second — `wallCount(s) +
wallCount(t·t) + 1 = 1 + 0 + 1 = 2`.  Contrast the r17 merge arm (whole `s·t·t` frame buried in one head wall → `1`
slot).  The canonical firing-block count, over a wire-changing body. -/
theorem whiskerLeftJunctionMuSlotCount : whiskerLeftJunctionMuWitness.1.pairs.length = 2 := rfl

/-! ## Observability -/

-- The junction witness slot count (expect `2`: the `s`-wall slot + the `mu` junction gap).
#eval whiskerLeftJunctionMuWitness.1.pairs.length

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the CONV-level whiskerLeft JUNCTION MERGE + its CANONICAL FACTORIZATION SHIP (WP-AMALG-2
r21, B1, arm b).**  `= true`.  `whiskerLeftFiringBlockMerge` proves `whiskerLeft (gapDomLayout nil frameBlocks)
(gapVcompLayout finalWall bodyPairs)` saturated-convertible to the layout splice (up to the boundary-distribution cast),
structurally on the frame's `AllIdBlocks` witness — the SINGLE-block case the r17 cell merge
`whiskerLeft_conv_mergeFrameIntoHead`, the cons case peeling the head frame block by `whiskerLeftComp` + threading the
IH + re-folding the head block via `whiskerLeft_conv_hcompIdLeading` + `vcompIdLeft`.  `whiskerLeftFiringBlockMergeAtFrame`
re-anchors it to a named frame 1-cell (the r19 round-trip `oneCell = gapDomLayout nil (firingBlockLayout oneCell)`), and
`whiskerLeftJunctionCanonical` assembles the `CanonicalFactorization (whiskerLeft oneCell body)` from a body factorization
— `pairs = spliceFrameIntoLayout (firingBlockLayout oneCell) bodyFact.pairs`, the CANONICAL slot count
`wallCount(oneCell) + wallCount(dom body) + 1`, the boundary distributions re-anchored, the conv threading `bodyFact.conv`
under `whiskerLeftCongr` then the merge, casts reconciled by `castBoundary_trans` + proof irrelevance.  Non-vacuous over a
WIRE-CHANGING body: `whiskerLeftJunctionMuWitness` (`s`-wall over `gen mu`) reads `2` canonical slots
(`whiskerLeftJunctionMuSlotCount`, `rfl`).

This is the recon's arm-b deliverable.  It does NOT flip `fxAmalg_whiskerJunctionMergeStaysWalled` by itself — that flips
only when BOTH arm b AND arm b' (the whiskerRight dual) literally ship (tracked in the ceiling ledger).  #2043 does NOT
close.  `= true`. -/
def fxAmalg_hasWhiskerLeftJunctionCanonical : Bool := true

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
