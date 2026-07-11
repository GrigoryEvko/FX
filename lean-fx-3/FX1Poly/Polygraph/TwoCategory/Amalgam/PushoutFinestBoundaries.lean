import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestPairs

/-! # Polygraph/TwoCategory/Amalgam/PushoutFinestBoundaries — the finest layout presents its 1-cell on ALL THREE
boundaries (dom = mid = cod), the Finding-A first-zip prerequisite (WP-AMALG-2 r12)

`PushoutFinestPairs.lean` (r11) shipped the cell-carrying `finestLayout` and its DOMAIN round-trip
`gapDomLayout_finestLayout` (`gapDomLayout nil ∘ finestLayout = id`).  The r9 vcomp SEAM (`pushoutFactorizeVcompSeam`)
DEMANDS both halves of a `vcomp` share ONE `(finalWall, pairs)` layout at their common middle 1-cell `G` — Finding-A.
Its clean structural prerequisite: `finestLayout G` must present `G` on ALL THREE boundaries (domain, MIDDLE, and
codomain), so it is a legal shared `pairs` for BOTH sides of the vcomp (the upper cell's codomain and the lower cell's
domain both being `G`).

## What ships — the middle and codomain round-trips

Every `finestLetterPair` sets `gapDom = gapMid = gapCod` (a wall letter puts the letter in `.wall` with all three gap
fields `nil`; a gap letter puts it in all three gap fields identically).  So the middle and codomain layouts of
`finestLayout` are WORD-IDENTICAL to the domain layout — `gapMidLayout_finestLayout` and `gapCodLayout_finestLayout`
are near-copies of the shipped `gapDomLayout_finestLayout`, proved by the SAME word route
(`pushoutPathWord_composePath` + `pushoutPathWord_pushoutEndoPathOfWord`, lifted by `pushoutPathWord_injective`),
differing only in swapping `gapDomLayout` for `gapMidLayout` / `gapCodLayout`.  Together with the shipped domain
round-trip this establishes: **`finestLayout G` presents `G` as dom = mid = cod**.

## What STAYS WALLED (no flip)

This is the STRUCTURAL prerequisite (all-boundary round-trips with identity cell payloads) — NOT the payload-carrying
finest common-refinement zip (the genuine Finding-A cell-level re-slice, which re-expresses two payload-bearing
factorizations against `finestLayout G`'s slots), NOT `wallFreeCellInvert`'s backward round-trip.  Those are the named
downstream nodes.  `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false`; `fxAmalg_hasGeneralPushoutDispatch` STAYS
`false`; `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL on the path / word.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The middle-boundary round-trip -/

/-- Each finest pair contributes exactly its one letter to the MIDDLE layout's word — the middle mirror of the shipped
`finestLetterPair_gapDomWord` (each pair's `gapMid` equals its `gapDom`: `nil` for a wall, the transported single
letter for a gap). -/
theorem finestLetterPair_gapMidWord {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (letter : involutionMonadPushout.Modality sourceMode targetMode)
    (rest : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) :
    pushoutPathWord (gapMidLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (finestLetterPair letter :: rest))
      = letter.val :: pushoutPathWord (gapMidLayout
          (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest) := by
  unfold finestLetterPair
  cases hTag : letterTag involutionMonadSplit letter.val
  · show pushoutPathWord (composePath (pushoutEndoPathOfWord [letter.val])
          (gapMidLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest))
        = letter.val :: pushoutPathWord (gapMidLayout
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest)
    rw [pushoutPathWord_composePath, pushoutPathWord_pushoutEndoPathOfWord]; rfl
  · show pushoutPathWord (composePath (pushoutEndoPathOfWord [letter.val])
          (gapMidLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest))
        = letter.val :: pushoutPathWord (gapMidLayout
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest)
    rw [pushoutPathWord_composePath, pushoutPathWord_pushoutEndoPathOfWord]; rfl

/-- The middle layout of `finestLayout` reads the original boundary word — the middle mirror of
`pushoutPathWord_finestLayout`. -/
theorem pushoutPathWord_finestLayoutMid :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    pushoutPathWord (gapMidLayout
        (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) (finestLayout path))
      = pushoutPathWord path
  | _, _, .nil _ => rfl
  | _, _, .cons letter rest =>
      (finestLetterPair_gapMidWord letter (finestLayout rest)).trans
        (congrArg (letter.val :: ·) (pushoutPathWord_finestLayoutMid rest))

/-- ★★★ **THE MIDDLE ROUND-TRIP** — `gapMidLayout nil ∘ finestLayout = id` on endo paths, lifted from the word-level
round-trip by the r11 reflection `pushoutPathWord_injective`.  So the finest layout's MIDDLE boundary reconstructs the
original 1-cell. -/
theorem gapMidLayout_finestLayout
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    gapMidLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (finestLayout path)
      = path :=
  pushoutPathWord_injective _ path (pushoutPathWord_finestLayoutMid path)

/-! ## The codomain-boundary round-trip -/

/-- Each finest pair contributes exactly its one letter to the CODOMAIN layout's word — the codomain mirror of the
shipped `finestLetterPair_gapDomWord`. -/
theorem finestLetterPair_gapCodWord {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (letter : involutionMonadPushout.Modality sourceMode targetMode)
    (rest : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) :
    pushoutPathWord (gapCodLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (finestLetterPair letter :: rest))
      = letter.val :: pushoutPathWord (gapCodLayout
          (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest) := by
  unfold finestLetterPair
  cases hTag : letterTag involutionMonadSplit letter.val
  · show pushoutPathWord (composePath (pushoutEndoPathOfWord [letter.val])
          (gapCodLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest))
        = letter.val :: pushoutPathWord (gapCodLayout
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest)
    rw [pushoutPathWord_composePath, pushoutPathWord_pushoutEndoPathOfWord]; rfl
  · show pushoutPathWord (composePath (pushoutEndoPathOfWord [letter.val])
          (gapCodLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest))
        = letter.val :: pushoutPathWord (gapCodLayout
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest)
    rw [pushoutPathWord_composePath, pushoutPathWord_pushoutEndoPathOfWord]; rfl

/-- The codomain layout of `finestLayout` reads the original boundary word — the codomain mirror of
`pushoutPathWord_finestLayout`. -/
theorem pushoutPathWord_finestLayoutCod :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    pushoutPathWord (gapCodLayout
        (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) (finestLayout path))
      = pushoutPathWord path
  | _, _, .nil _ => rfl
  | _, _, .cons letter rest =>
      (finestLetterPair_gapCodWord letter (finestLayout rest)).trans
        (congrArg (letter.val :: ·) (pushoutPathWord_finestLayoutCod rest))

/-- ★★★ **THE CODOMAIN ROUND-TRIP** — `gapCodLayout nil ∘ finestLayout = id` on endo paths, lifted by
`pushoutPathWord_injective`.  So the finest layout's CODOMAIN boundary reconstructs the original 1-cell — with the
shipped domain round-trip and `gapMidLayout_finestLayout` this makes `finestLayout G` present `G` on all three
boundaries (dom = mid = cod), the legal shared layout the r9 vcomp seam consumes on BOTH sides. -/
theorem gapCodLayout_finestLayout
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    gapCodLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (finestLayout path)
      = path :=
  pushoutPathWord_injective _ path (pushoutPathWord_finestLayoutCod path)

/-! ## Concrete probe -/

/-- ★★ **CONCRETE PROBE.**  The witness 1-cell `s·t·s·t·t` has its finest layout's MIDDLE and CODOMAIN boundaries both
reconstruct it — the finest layout presents the witness on all three boundaries. -/
theorem finestLayoutWitnessAllBoundaries :
    gapMidLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout (pushoutEndoPathOfWord witnessWord))
        = pushoutEndoPathOfWord witnessWord
      ∧ gapCodLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout (pushoutEndoPathOfWord witnessWord))
        = pushoutEndoPathOfWord witnessWord :=
  ⟨gapMidLayout_finestLayout (pushoutEndoPathOfWord witnessWord),
    gapCodLayout_finestLayout (pushoutEndoPathOfWord witnessWord)⟩

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the finest layout presents its 1-cell on ALL THREE boundaries (WP-AMALG-2 r12, Finding-A
first-zip).**  `= true`: the MIDDLE round-trip (`gapMidLayout_finestLayout`) and the CODOMAIN round-trip
(`gapCodLayout_finestLayout`), each a near-copy of the shipped `gapDomLayout_finestLayout` (same word route, swapping
`gapDomLayout` for `gapMidLayout` / `gapCodLayout`), with the concrete witness probe.  Together with the shipped
domain round-trip this establishes `finestLayout G` presents `G` as dom = mid = cod — the legal shared `(finalWall,
pairs)` the r9 vcomp seam consumes on BOTH halves of a `vcomp`.  It ships the STRUCTURE (all-boundary round-trips,
identity cell payloads), NOT the payload-carrying finest common-refinement zip (the genuine Finding-A cell re-slice).
No marker flips.  `= true`. -/
def fxAmalg_hasFinestAllBoundaryRoundTrips : Bool := true

end FX1Poly.Polygraph.Amalgam
