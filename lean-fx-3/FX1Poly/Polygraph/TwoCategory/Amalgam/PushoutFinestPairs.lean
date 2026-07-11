import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutEndoModeTransport
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalLayout
import FX1Poly.Polygraph.TwoCategory.Amalgam.Witness

/-! # Polygraph/TwoCategory/Amalgam/PushoutFinestPairs — the cell-carrying FINEST layout `finestLayout`, feeding the
r9 seam (Finding B), on the r11 transport (WP-AMALG-2 r11, B3 — the r10 ledger's B2 node)

The r10 ledger named `finestLayout` — "the cell-carrying pairs (Finding B) — `finestLayout : path → List
VcompGapPair` with `gapDomLayout finalWall ∘ finestLayout = id`" — with the WIDTH shape (`finestGapWidths`, r9) and
its merge law (r10) shipped, but "the PAIRS producer walled by the SAME single-mode transport (a per-letter block's
`wall` / `gapDom` must be an endo path `monadPushMode → monadPushMode`, but path letters carry
provably-but-not-syntactically-single intermediate modes)."  `PushoutEndoModeTransport.lean` (r11 B1) authored that
transport; this file builds the pairs producer on it.

## `finestLayout` — the per-letter cell-carrying pairs

`finestLayout` reads the pushout 1-cell letter-by-letter, emitting one `VcompGapPair` PER LETTER: an `s`-WALL letter
(`letterTag = true`) becomes a pair carrying it in the `wall` field (`wallLetterPair`, empty gap); a `t`-GAP letter
(`letterTag = false`) becomes a pair carrying it in the `gapDom` field with identity payload (`gapLetterPair`).  Each
single-letter endo path is built by the r11 transport `pushoutEndoPathOfWord [letter.val]`, so every `VcompGapPair`
field is an endo path at `monadPushMode` — the middle mode never entering (the transport's output type is fixed
endo).  This is the PER-LETTER granularity: the MAXIMAL refinement, one slot per letter — it REFINES the r9
wall-count-keyed slot shape (`finestGapWidths`, whose slot count is `wallCount + 1`, merging maximal `t`-runs).  The
wall/gap TAGGING (`s` in `.wall`, `t` in `.gapDom`) is the free-product alternating structure, preserved per-letter.

## The domain round-trip, via the r11 reflection

`gapDomLayout_finestLayout` (`gapDomLayout nil ∘ finestLayout = id` on endo paths) is proved at the WORD level then
lifted by the r11 reflection `pushoutPathWord_injective`.  At the word level: `pushoutPathWord_composePath` (the
boundary-word monoid homomorphism, new here) turns each pair's `wall · gapDom` contribution into `[letter.val]`
(exactly one letter, whichever field it sits in — the other is `nil`, absorbed by `composePath nil`), so
`finestLetterPair_gapDomWord` gives `letter.val :: …` and `pushoutPathWord_finestLayout` folds the layout's word
back to `pushoutPathWord path`.  No `castBoundary`, no middle-mode `Eq.rec`.

## What STAYS WALLED (no flip)

This ships the PAIRS producer + the domain round-trip — NOT the genuine cell payloads the r9 vcomp SEAM fires
through (the pairs here carry IDENTITY payloads, the shape not the content), NOT the vcomp-case COMMON-REFINEMENT zip
(Finding-A), NOT `wallFreeCellInvert`.  Those are downstream nodes.  `fxAmalg_hasFullSaturatedPushoutDispatch`
(`DispatchSaturated.lean`) STAYS `false`; `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL on the path / word.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The boundary-word monoid homomorphism -/

/-- ★ **`pushoutPathWord` is a MONOID HOMOMORPHISM** — the boundary word of a path composite is the concatenation of
the boundary words (structural on the first path; `composePath` recurses on the first, so `nil` is `rfl` — `[] ++ w =
w` definitionally — and `cons` is a `congrArg`).  The word-level engine for the layout round-trip. -/
theorem pushoutPathWord_composePath :
    {sourceMode middleMode targetMode : Fin involutionMonadPushout.modeCount} →
    (first : ModalityPath involutionMonadPushout.toModeGraph sourceMode middleMode) →
    (second : ModalityPath involutionMonadPushout.toModeGraph middleMode targetMode) →
    pushoutPathWord (composePath first second) = pushoutPathWord first ++ pushoutPathWord second
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons letter rest, second =>
      congrArg (letter.val :: ·) (pushoutPathWord_composePath rest second)

/-! ## The per-letter cell-carrying pairs -/

/-- The **wall pair** carrying a single `s`-wall letter in the `wall` field (empty gap, identity payload) — an
endo-at-`monadPushMode` `VcompGapPair` built via the r11 transport. -/
def wallLetterPair {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (letter : involutionMonadPushout.Modality sourceMode targetMode) :
    VcompGapPair involutionMonadPushout.toModeSignature monadPushMode where
  wall := pushoutEndoPathOfWord [letter.val]
  gapDom := ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode
  gapMid := ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode
  gapCod := ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode
  upper := RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature)
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
  lower := RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature)
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)

/-- The **gap pair** carrying a single `t`-gap letter in the `gapDom` field (with `gapMid = gapCod = gapDom` and
identity payload) — an endo-at-`monadPushMode` `VcompGapPair` built via the r11 transport. -/
def gapLetterPair {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (letter : involutionMonadPushout.Modality sourceMode targetMode) :
    VcompGapPair involutionMonadPushout.toModeSignature monadPushMode where
  wall := ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode
  gapDom := pushoutEndoPathOfWord [letter.val]
  gapMid := pushoutEndoPathOfWord [letter.val]
  gapCod := pushoutEndoPathOfWord [letter.val]
  upper := RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature)
    (pushoutEndoPathOfWord [letter.val])
  lower := RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature)
    (pushoutEndoPathOfWord [letter.val])

/-- The **finest per-letter pair** — a `wallLetterPair` for a wall (`letterTag = true`), a `gapLetterPair` for a gap
(`letterTag = false`).  `bif` on the tag (Bool `cond`, reduces on a known tag). -/
def finestLetterPair {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (letter : involutionMonadPushout.Modality sourceMode targetMode) :
    VcompGapPair involutionMonadPushout.toModeSignature monadPushMode :=
  bif letterTag involutionMonadSplit letter.val then wallLetterPair letter else gapLetterPair letter

/-- ★★★ **THE CELL-CARRYING FINEST LAYOUT.**  A pushout 1-cell reads to its list of per-letter `VcompGapPair`s (one
per letter, wall or gap by `letterTag`).  Structural on the path; the empty path is the empty layout.  This is the
r10 ledger's B2 node — the pairs producer, unblocked by the r11 transport (every pair field an endo path at the
single mode). -/
def finestLayout : {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode →
    List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)
  | _, _, .nil _ => []
  | _, _, .cons letter rest => finestLetterPair letter :: finestLayout rest

/-! ## The domain round-trip -/

/-- ★★ **Each finest pair contributes exactly its one letter to the domain layout's word.**  Whether the letter is a
wall (in `.wall`, `.gapDom = nil`) or a gap (in `.gapDom`, `.wall = nil`), the `nil` field is absorbed by
`composePath nil` and the layout's leading contribution is `letter.val`.  `bif`-cased on the tag; each case a
`composePath` word homomorphism through the transported single letter. -/
theorem finestLetterPair_gapDomWord {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (letter : involutionMonadPushout.Modality sourceMode targetMode)
    (rest : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)) :
    pushoutPathWord (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (finestLetterPair letter :: rest))
      = letter.val :: pushoutPathWord (gapDomLayout
          (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest) := by
  unfold finestLetterPair
  cases hTag : letterTag involutionMonadSplit letter.val
  · show pushoutPathWord (composePath (pushoutEndoPathOfWord [letter.val])
          (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest))
        = letter.val :: pushoutPathWord (gapDomLayout
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest)
    rw [pushoutPathWord_composePath, pushoutPathWord_pushoutEndoPathOfWord]; rfl
  · show pushoutPathWord (composePath (pushoutEndoPathOfWord [letter.val])
          (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest))
        = letter.val :: pushoutPathWord (gapDomLayout
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest)
    rw [pushoutPathWord_composePath, pushoutPathWord_pushoutEndoPathOfWord]; rfl

/-- ★★ **The domain layout of `finestLayout` reads the original boundary word** — `pushoutPathWord (gapDomLayout nil
(finestLayout path)) = pushoutPathWord path`.  Structural on the path, each `cons` peeling one letter via
`finestLetterPair_gapDomWord` and recursing.  The WORD-level round-trip. -/
theorem pushoutPathWord_finestLayout :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    pushoutPathWord (gapDomLayout
        (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) (finestLayout path))
      = pushoutPathWord path
  | _, _, .nil _ => rfl
  | _, _, .cons letter rest =>
      (finestLetterPair_gapDomWord letter (finestLayout rest)).trans
        (congrArg (letter.val :: ·) (pushoutPathWord_finestLayout rest))

/-- ★★★ **THE DOMAIN ROUND-TRIP** — `gapDomLayout nil ∘ finestLayout = id` on endo paths.  The word-level round-trip
(`pushoutPathWord_finestLayout`) lifts to the path level by the r11 reflection `pushoutPathWord_injective`.  So the
finest per-letter layout's domain boundary reconstructs the original 1-cell — the r10 ledger's `gapDomLayout finalWall
∘ finestLayout = id` deliverable (with `finalWall = nil`, the per-letter layout having no separate trailing wall). -/
theorem gapDomLayout_finestLayout
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (finestLayout path)
      = path :=
  pushoutPathWord_injective _ path (pushoutPathWord_finestLayout path)

/-! ## Smoke + concrete probe -/

/-- ★ **The layout has one pair per letter** — `(finestLayout path).length = path.length`.  Structural `congrArg`.
The per-letter (maximal) granularity, made a length fact. -/
theorem finestLayout_length :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    (finestLayout path).length = path.length
  | _, _, .nil _ => rfl
  | _, _, .cons _letter rest => congrArg (· + 1) (finestLayout_length rest)

-- The finest layout of the witness path `s·t·s·t·t` has 5 pairs (one per letter). Expect `5`.
#eval (finestLayout (pushoutEndoPathOfWord witnessWord)).length

/-- ★★ **CONCRETE PROBE.**  The witness 1-cell `s·t·s·t·t` (transported from `witnessWord`) has its finest layout's
domain boundary reconstruct it (via the domain round-trip) — a genuine reduction on the concrete alternating word. -/
theorem finestLayoutWitnessProbe :
    gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (finestLayout (pushoutEndoPathOfWord witnessWord))
      = pushoutEndoPathOfWord witnessWord :=
  gapDomLayout_finestLayout (pushoutEndoPathOfWord witnessWord)

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the cell-carrying FINEST layout `finestLayout` + the domain round-trip SHIP (WP-AMALG-2
r11, B3).**  `= true`: the boundary-word monoid homomorphism (`pushoutPathWord_composePath`), the per-letter pairs
(`wallLetterPair` / `gapLetterPair` / `finestLetterPair`, each field an endo path via the r11 transport), the layout
producer `finestLayout`, and the DOMAIN ROUND-TRIP `gapDomLayout_finestLayout` (`gapDomLayout nil ∘ finestLayout =
id`, at the WORD level via `pushoutPathWord_finestLayout` + the r11 reflection `pushoutPathWord_injective`), with the
one-pair-per-letter smoke (`finestLayout_length`) and the concrete witness probe (`finestLayoutWitnessProbe`, the
`s·t·s·t·t` 1-cell reconstructs).  This is the r10 ledger's B2 node — the pairs producer, unblocked by the r11
transport.  It ships the SHAPE (identity cell payloads, per-letter granularity refining the r9 wall-count slot
shape), NOT the genuine seam-firing payloads, the vcomp COMMON-REFINEMENT zip (Finding-A), or `wallFreeCellInvert`.
No marker flips.  `= true`. -/
def fxAmalg_hasFinestPairsLayout : Bool := true

end FX1Poly.Polygraph.Amalgam
