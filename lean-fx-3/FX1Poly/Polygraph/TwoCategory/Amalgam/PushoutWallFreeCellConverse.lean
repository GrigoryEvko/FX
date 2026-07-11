import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutEndoModeTransport
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallCountInvariance

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallFreeCellConverse — the wall-free CELL converse `wallFreeCellInvert`:
its clean structural prerequisites SHIP; the full four-case reconstruction is the honest r12 deferral
(WP-AMALG-2 r11, B4 — the r10 ledger's B3 node)

The r10 ledger named `wallFreeCellInvert` (B3) — "the essential-surjectivity converse feeding
`pushoutRightImageConvReflect`: a wall-free-boundary pushout cell EXTRACTS a monad pre-image cell" — standing on
`pathInvert` (B2, now shipped) + `mapPath_inclRight_injective` (shipped).  The recon scopes its full four-case
structural recursion — and especially its BACKWARD round-trip (`mapCellAlong inclRight (wallFreeCellInvert cell) ≈
cell`) — as "cast-heavy … genuine multi-lemma LABOR", to r12.  This file ships the two CLEAN, zero-axiom structural
PREREQUISITES that recursion stands on, and names the residual precisely.

## What ships — the wall-free / wall-count BRIDGE and dom-to-cod preservation

The r11 transport's wall-free hypothesis `pathWallFree` (per-letter, structural) is EXACTLY the r6 wall-count-zero
invariant:

  * **`wallCountZero_of_pathWallFree`** — a wall-free 1-cell has `pushoutPathWallCount = 0` (every letter tags
    component-2, contributing `0`).
  * **`pathWallFree_of_wallCountZero`** — conversely, a wall-count-`0` 1-cell is wall-free (each `wallBitCount` in
    the sum being `0` forces each letter's tag `false`; a `true` letter would contribute `1`, refuted by
    `Nat.noConfusion`).

Their consequence is the vcomp-case ingredient of the cell converse:

  * **`wallFreeMiddleOfCell`** — for ANY pushout 2-cell `cell : sourcePath ⇒ targetPath`, a wall-free SOURCE forces
    a wall-free TARGET.  Immediate from the r6 dom-to-cod wall-count conservation (`wallLetterCount_dom_eq_cod`)
    threaded through the bridge.  This is precisely what the cell converse's `vcomp` case needs to descend into both
    halves (the middle 1-cell `G` of `α : F ⇒ G`, `β : G ⇒ H` is wall-free when `F` is), and a genuine standalone
    fact: wall-freeness is a dom-to-cod-STABLE property of pushout 2-cells.

## What STAYS WALLED — the honest r12 deferral, with the EXACT goal

The full `wallFreeCellInvert : (cell : RawTwoCellExpr pushout.toModeSignature sourcePath targetPath) → pathWallFree
sourcePath → pathWallFree targetPath → RawTwoCellExpr monadComputad.toModeSignature (pathInvert sourcePath _)
(pathInvert targetPath _)` is a structural recursion on the cell whose cases are:

  * **`id`** — `id (pathInvert path _)` (proof-irrelevant `pathInvert`); clean GIVEN `pathInvert`.
  * **`vcomp`** — recurse on both halves, the middle 1-cell's wall-freeness supplied by `wallFreeMiddleOfCell`
    (shipped here); clean GIVEN `pathInvert`.
  * **`gen`** — the CRUX: a pushout 2-generator (a retagged monad `eta` / `mu`, index in `Fin 2`) must reconstruct
    its MONAD 2-generator at boundary `(pathInvert sourcePath, pathInvert targetPath)` — the CONVERSE of
    `interpretWordFrom_map` (the engine of `inclusionRightTwoReal`, itself a whole file), riding one
    `Option.some.inj` + `mapCellAlong_castBoundary` + `SaturatedConvOver.castBoundaryCongr`.  Cast-heavy.
  * **`whiskerLeft` / `whiskerRight`** — boundary reconciliation across `mapPath_composePath` junction casts.

and whose BACKWARD round-trip (`mapCellAlong inclRight ∘ wallFreeCellInvert ≈ id`) is a `reseatCellInv`-style
multi-lemma assembly the recon flags as "LABOR, not undecidability".  Named node: **the four-case
`wallFreeCellInvert` structural recursion (the `gen` monad-2-generator reseat = converse of `interpretWordFrom_map`,
plus the whisker junction casts) + its backward round-trip** — scoped to r12 (it balloons past one file).

## No flip

`fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`;
`fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL on the path.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The wall-free / wall-count bridge -/

/-- ★★ **A wall-free 1-cell has wall count `0`** — every letter tags component-2 (`wallFree.1 : letterTag = false`,
so `wallBitCount = 0`), and the tail recurses.  Structural on the path (`Nat.zero_add` at the head, clean).  Ties the
r11 transport's `pathWallFree` hypothesis to the r6 wall-count invariant (the SOUND direction). -/
theorem wallCountZero_of_pathWallFree :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    pathWallFree path → pushoutPathWallCount path = 0
  | _, _, .nil _, _ => rfl
  | _, _, .cons letter rest, wallFree => by
      show wallBitCount (letterTag involutionMonadSplit letter.val) + pushoutPathWallCount rest = 0
      rw [wallFree.1]
      show (0 : Nat) + pushoutPathWallCount rest = 0
      rw [Nat.zero_add, wallCountZero_of_pathWallFree rest wallFree.2]

/-- ★★ **A wall-count-`0` 1-cell is wall-free** — the converse.  Structural on the path: casing the head letter's
tag, a `false` head gives the first conjunct and (via `Nat.zero_add`) the tail's wall count `0` to recurse; a `true`
head would contribute `wallBitCount true = 1` to the sum, so `1 + tailCount = 0` is refuted by `Nat.noConfusion`
(after `Nat.add_comm`, propext-free — NOT `Nat.succ_ne_zero`).  With `wallCountZero_of_pathWallFree` this makes
`pathWallFree` and `pushoutPathWallCount = 0` EQUIVALENT. -/
theorem pathWallFree_of_wallCountZero :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    pushoutPathWallCount path = 0 → pathWallFree path
  | _, _, .nil _, _ => True.intro
  | _, _, .cons letter rest, hzero => by
      have hexpand : wallBitCount (letterTag involutionMonadSplit letter.val)
          + pushoutPathWallCount rest = 0 := hzero
      cases hTag : letterTag involutionMonadSplit letter.val with
      | false =>
          rw [hTag] at hexpand
          exact ⟨hTag, pathWallFree_of_wallCountZero rest
            ((Nat.zero_add (pushoutPathWallCount rest)) ▸ hexpand)⟩
      | true =>
          rw [hTag] at hexpand
          exact Nat.noConfusion ((Nat.add_comm 1 (pushoutPathWallCount rest)) ▸ hexpand)

/-! ## Wall-freeness is dom-to-cod stable — the vcomp-case ingredient -/

/-- ★★★ **Wall-freeness is DOM-TO-COD STABLE across every pushout 2-cell.**  For ANY `cell : sourcePath ⇒
targetPath`, a wall-free SOURCE forces a wall-free TARGET — immediate from the r6 wall-count conservation
(`wallLetterCount_dom_eq_cod`) threaded through the bridge (`wallCountZero_of_pathWallFree` then
`pathWallFree_of_wallCountZero`).  This is EXACTLY the ingredient the cell converse's `vcomp` case needs: the middle
1-cell `G` of a vertical composite `α : F ⇒ G`, `β : G ⇒ H` is wall-free when `F` is, so BOTH halves recurse. -/
theorem wallFreeMiddleOfCell
    {sourceMode targetMode : involutionMonadPushout.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath)
    (sourceWallFree : pathWallFree sourcePath) :
    pathWallFree targetPath :=
  pathWallFree_of_wallCountZero targetPath
    ((wallLetterCount_dom_eq_cod cell).symm.trans
      (wallCountZero_of_pathWallFree sourcePath sourceWallFree))

/-! ## Concrete probe -/

/-- ★★ **CONCRETE PROBE.**  The pushout unit `eta : id ⇒ t` has a wall-free DOMAIN (`id = nil`, vacuously
wall-free), so its CODOMAIN `t` (`monadPushTPath`) is wall-free by `wallFreeMiddleOfCell` — the wire-creating `eta`
stays inside the gap component, creating no wall. -/
theorem wallFreeMiddleOfCell_probe : pathWallFree monadPushTPath :=
  wallFreeMiddleOfCell pushoutEta True.intro

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the wall-free CELL converse's clean prerequisites SHIP; the full reconstruction is the
r12 deferral (WP-AMALG-2 r11, B4).**  `= true`: the wall-free / wall-count BRIDGE (`wallCountZero_of_pathWallFree` +
`pathWallFree_of_wallCountZero`, making the r11 transport's `pathWallFree` hypothesis EQUIVALENT to the r6
wall-count-zero invariant) and dom-to-cod STABILITY (`wallFreeMiddleOfCell`: a wall-free source forces a wall-free
target across any pushout 2-cell, the `vcomp`-case ingredient), with the concrete `eta` probe.  These are the clean
structural prerequisites the four-case `wallFreeCellInvert` recursion stands on.  It ships the PREREQUISITES, NOT the
converse itself.  `= true`. -/
def fxAmalg_hasWallFreeCellConversePrereqs : Bool := true

/-- ★★ **Honesty marker — the full `wallFreeCellInvert` (the CELL-level essential-surjectivity converse) STAYS
WALLED to r12.**  `= true` (the wall honestly held, precisely named).  The four-case structural recursion
(`id`/`vcomp` clean GIVEN `pathInvert` + `wallFreeMiddleOfCell`; the `gen` case the CRUX — a retagged monad `eta`/`mu`
2-generator reconstructing its monad 2-generator at the `pathInvert` boundary, the CONVERSE of `interpretWordFrom_map`
riding `mapCellAlong_castBoundary` + `SaturatedConvOver.castBoundaryCongr`; the whisker cases across
`mapPath_composePath` junction casts) plus the BACKWARD round-trip (`mapCellAlong inclRight ∘ wallFreeCellInvert ≈
id`, a `reseatCellInv`-style multi-lemma assembly) is cast-heavy LABOR that balloons past one file — scoped to r12,
NOT undecidability.  This round ships its clean structural prerequisites (the bridge + dom-to-cod stability), not the
converse.  `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false`.  No fabricated flip.  `= true`. -/
def fxAmalg_wallFreeCellInvertStaysWalled : Bool := true

end FX1Poly.Polygraph.Amalgam
