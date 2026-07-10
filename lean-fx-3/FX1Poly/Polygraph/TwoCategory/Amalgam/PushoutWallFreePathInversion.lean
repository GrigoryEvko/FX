import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutEndoModeTransport
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreePathInjectivity

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallFreePathInversion — the wall-free 1-cell CONVERSE `pathInvert`, its
two round-trips assembled on the transport + the shipped injectivity (WP-AMALG-2 r11, B2 — the r10 ledger's B1 node)

The r10 ledger named `pathInvert` — "the wall-free 1-cell CONVERSE (a pushout wall-free path reconstructs a MONAD
path, with `mapPath inclRight ∘ pathInvert = id`)" — with its INJECTIVITY (the faithfulness half,
`mapPath_inclRight_injective`) SHIPPED and its ESSENTIAL-SURJECTIVITY half "walled by the SINGLE-MODE
intermediate-mode transport."  `PushoutEndoModeTransport.lean` (r11 B1) authored that transport; this file assembles
`pathInvert` on top of it and closes BOTH round-trips.

## `pathInvert` — the reconstruction, `Eq.rec`-free

Because the reconstructed MONAD path is always an ENDO at the single monad mode `monadOnlyMode`, `pathInvert` is a
clean STRUCTURAL recursion on the pushout path whose OUTPUT type is fixed endo — the pushout's variable middle mode
NEVER enters the output, so there is no `Eq.rec`-through-a-type-level-function.  Each `cons` letter, wall-free
(`letterTag = false`, i.e. `comp1.len ≤ .val`), retracts by the shipped `retractRightLetter` (its `isRight` from
`geOfBltFalse`) to a monad 1-generator, tagged endo by `monadGenEndpoints`.

## The two round-trips (word route + the shipped injectivities)

  * **`mapPath_inclRight_pathInvert`** (FORWARD, `mapPath inclRight ∘ pathInvert = id` on endo paths) — proved at
    the WORD level then lifted by the r11 reflection `pushoutPathWord_injective`: the mapped-then-read word is the
    shipped `mapPath_inclRight_word` retag of the monad word, and `monadEmbedInvert_word` cancels
    `embedRightLetter ∘ retractRightLetter` (the shipped `embedRightLetter_retractRightLetter`) letter-by-letter to
    recover `pushoutPathWord path`.  No `castBoundary`, no `Eq.rec`.
  * **`pathInvert_mapPath_inclRight`** (REVERSE, `pathInvert ∘ mapPath inclRight = id` on monad paths) — every
    right-coprojected monad path is wall-free (`mapPath_inclRight_wallFree`, via `embedRightLetter_component`), and
    the shipped FAITHFULNESS `mapPath_inclRight_injective` cancels `mapPath inclRight` off the forward round-trip.

Together `pathInvert` + `mapPath_inclRight_injective` is a genuine BIJECTION between monad 1-cells and the wall-free
pushout 1-cells at the single mode — node (i)'s 1-cell essential-surjectivity converse, delivered.

## What STAYS WALLED (no flip)

This is the 1-CELL converse — NOT the CELL-level `wallFreeCellInvert` (node i's essential-surjectivity converse
feeding `pushoutRightImageConvReflect`), NOT `finestLayout` (the cell-carrying pairs, B3).  Those are the named
downstream nodes.  `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`;
`fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL on the path / word.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The monad-side single mode and its endo generators -/

/-- The single mode of the walking-monad component (`Fin monadComputad.modeCount`, the sole inhabitant). -/
def monadOnlyMode : Fin monadComputad.modeCount := ⟨0, by decide⟩

/-- Every monad 1-generator is an ENDO at `monadOnlyMode` — the monad computad has one endo-generator `t`, so any
index (necessarily `⟨0, _⟩`) has recorded endpoints `(monadOnlyMode, monadOnlyMode)` by `rfl`; the impossible
`⟨count + 1, _⟩` index is discharged propext-free (`Nat.not_lt_zero`, NOT `Fin.cases`). -/
theorem monadGenEndpoints (index : Fin monadComputad.modalityGenerators.length) :
    monadComputad.modalityGenerators.get index = (monadOnlyMode, monadOnlyMode) :=
  match index with
  | ⟨0, _⟩ => rfl
  | ⟨count + 1, isLt⟩ => False.elim (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ isLt))

/-- The **monad letter recovered from a wall-free pushout letter** — a component-2 (`letterTag = false`) pushout
letter retracts (by the shipped `retractRightLetter`, its `isRight` from `geOfBltFalse`) to a monad 1-generator
index, tagged endo at `monadOnlyMode` by `monadGenEndpoints`.  The letter-level content of the converse. -/
def monadLetterOfWallFree {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (letter : involutionMonadPushout.Modality sourceMode targetMode)
    (wallFree : letterTag involutionMonadSplit letter.val = false) :
    monadComputad.Modality monadOnlyMode monadOnlyMode :=
  ⟨retractRightLetter involutionComputad monadComputad involutionMonadSameModes letter.val
      (geOfBltFalse wallFree),
    monadGenEndpoints _⟩

/-! ## `pathInvert` — the wall-free 1-cell converse -/

/-- ★★★ **THE WALL-FREE 1-CELL CONVERSE.**  A wall-free pushout 1-cell reconstructs a MONAD 1-cell.  STRUCTURAL on
the pushout path, each wall-free `cons` letter retracting to a monad letter (`monadLetterOfWallFree`) and the tail
recursing.  The OUTPUT type is fixed endo at `monadOnlyMode`, so the pushout's variable middle mode never enters —
no `Eq.rec`-through-a-type-level-function, no childCons drilling.  This is node (i)'s 1-cell essential-surjectivity
converse, standing on the r11 transport (the endo output) + the shipped letter retract. -/
def pathInvert : {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    pathWallFree path → ModalityPath monadComputad.toModeGraph monadOnlyMode monadOnlyMode
  | _, _, .nil _, _ => ModalityPath.nil (graph := monadComputad.toModeGraph) monadOnlyMode
  | _, _, .cons letter rest, wallFreeHyp =>
      ModalityPath.cons (monadLetterOfWallFree letter wallFreeHyp.1) (pathInvert rest wallFreeHyp.2)

/-! ## The forward round-trip, via the word route -/

/-- ★★ **The word-level round-trip helper** — retagging `pathInvert`'s monad word by `embedRightLetter` recovers the
original pushout boundary word: `(monadPathWord (pathInvert path wallFree)).map embedRightLetter = pushoutPathWord
path`.  Structural on the path; the `cons` case cancels `embedRightLetter ∘ retractRightLetter` on the head (the
shipped `embedRightLetter_retractRightLetter`) and recurses on the tail — all at the WORD level (non-dependent), so
no middle-mode landmine. -/
theorem monadEmbedInvert_word :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    (wallFree : pathWallFree path) →
    (monadPathWord (pathInvert path wallFree)).map
        (embedRightLetter involutionComputad monadComputad involutionMonadSameModes)
      = pushoutPathWord path
  | _, _, .nil _, _ => rfl
  | _, _, .cons letter rest, wallFree =>
      (congrArg
        (embedRightLetter involutionComputad monadComputad involutionMonadSameModes
            (retractRightLetter involutionComputad monadComputad involutionMonadSameModes letter.val
              (geOfBltFalse wallFree.1)) :: ·)
        (monadEmbedInvert_word rest wallFree.2)).trans
      (congrArg (· :: pushoutPathWord rest)
        (embedRightLetter_retractRightLetter involutionComputad monadComputad involutionMonadSameModes
          letter.val (geOfBltFalse wallFree.1)))

/-- ★★★ **THE FORWARD ROUND-TRIP** — `mapPath inclRight ∘ pathInvert = id` on wall-free endo pushout paths.  At the
WORD level `pushoutPathWord (mapPath inclRight (pathInvert path wallFree))` is the shipped `mapPath_inclRight_word`
retag of `monadPathWord (pathInvert …)`, which `monadEmbedInvert_word` returns to `pushoutPathWord path`; the r11
reflection `pushoutPathWord_injective` lifts that word equality to the path equality.  So a wall-free pushout 1-cell
IS the right-coprojection of its reconstructed monad pre-image. -/
theorem mapPath_inclRight_pathInvert
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    (wallFree : pathWallFree path) :
    mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes)
        (pathInvert path wallFree)
      = path :=
  pushoutPathWord_injective _ path
    ((mapPath_inclRight_word (pathInvert path wallFree)).trans (monadEmbedInvert_word path wallFree))

/-! ## The reverse round-trip, via the shipped faithfulness -/

/-- ★★ **Every right-coprojected monad path is WALL-FREE** — each mapped letter is `embedRightLetter`-tagged
component-2 (`embedRightLetter_component`).  Structural on the monad path.  The precondition the reverse round-trip
supplies to `pathInvert`. -/
theorem mapPath_inclRight_wallFree :
    {sourceMode targetMode : Fin monadComputad.modeCount} →
    (path : ModalityPath monadComputad.toModeGraph sourceMode targetMode) →
    pathWallFree (mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes) path)
  | _, _, .nil _ => True.intro
  | _, _, .cons modality rest =>
      ⟨embedRightLetter_component involutionComputad monadComputad involutionMonadSameModes modality.val,
        mapPath_inclRight_wallFree rest⟩

/-- ★★★ **THE REVERSE ROUND-TRIP** — `pathInvert ∘ mapPath inclRight = id` on monad paths.  A right-coprojected
monad path is wall-free (`mapPath_inclRight_wallFree`), so the forward round-trip gives `mapPath inclRight (pathInvert
(mapPath inclRight path) …) = mapPath inclRight path`, and the shipped FAITHFULNESS `mapPath_inclRight_injective`
cancels `mapPath inclRight`.  With the forward leg this makes `pathInvert` + `mapPath inclRight` a genuine BIJECTION
between monad 1-cells and wall-free pushout 1-cells at the single mode. -/
theorem pathInvert_mapPath_inclRight
    (path : ModalityPath monadComputad.toModeGraph monadOnlyMode monadOnlyMode) :
    pathInvert (mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes) path)
        (mapPath_inclRight_wallFree path)
      = path :=
  mapPath_inclRight_injective _ path
    (mapPath_inclRight_pathInvert
      (mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes) path)
      (mapPath_inclRight_wallFree path))

/-! ## Concrete round-trip probes (both directions) -/

/-- The concrete wall-free witness for the endo path `t·t`. -/
def tRunTwoWallFree : pathWallFree (composePath monadPushTPath monadPushTPath) :=
  ⟨by decide, by decide, True.intro⟩

/-- A concrete monad endo 1-generator `t` (index `0`, endo by `monadGenEndpoints`). -/
def monadEndoLetter : monadComputad.Modality monadOnlyMode monadOnlyMode :=
  ⟨⟨0, by decide⟩, monadGenEndpoints _⟩

/-- The concrete monad endo path `t·t` (monad side). -/
def monadEndoTwoT : ModalityPath monadComputad.toModeGraph monadOnlyMode monadOnlyMode :=
  ModalityPath.cons monadEndoLetter
    (ModalityPath.cons monadEndoLetter (ModalityPath.nil (graph := monadComputad.toModeGraph) monadOnlyMode))

-- The reconstructed monad word of the wall-free pushout path `t·t` — expect `[0, 0]` (two monad `t`-letters).
#eval (monadPathWord (pathInvert (composePath monadPushTPath monadPushTPath) tRunTwoWallFree)).map Fin.val

/-- ★★ **FORWARD concrete probe** — inverting the wall-free pushout endo path `t·t` and re-coprojecting recovers it
(a genuine reduction on concrete data, via the forward round-trip). -/
theorem pathInvert_forward_probe :
    mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes)
        (pathInvert (composePath monadPushTPath monadPushTPath) tRunTwoWallFree)
      = composePath monadPushTPath monadPushTPath :=
  mapPath_inclRight_pathInvert _ tRunTwoWallFree

/-- ★★ **REVERSE concrete probe** — coprojecting the monad endo path `t·t` then inverting recovers it. -/
theorem pathInvert_reverse_probe :
    pathInvert (mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes) monadEndoTwoT)
        (mapPath_inclRight_wallFree monadEndoTwoT)
      = monadEndoTwoT :=
  pathInvert_mapPath_inclRight monadEndoTwoT

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the wall-free 1-cell CONVERSE `pathInvert` + BOTH round-trips SHIP (WP-AMALG-2 r11, B2).**
`= true`: `pathInvert` (the reconstruction, `Eq.rec`-free — its endo output type makes the pushout middle mode
vanish), the forward round-trip `mapPath_inclRight_pathInvert` (`mapPath inclRight ∘ pathInvert = id`, via the word
helper `monadEmbedInvert_word` + the shipped `mapPath_inclRight_word` / `embedRightLetter_retractRightLetter` + the
r11 reflection `pushoutPathWord_injective`), and the reverse round-trip `pathInvert_mapPath_inclRight` (`pathInvert
∘ mapPath inclRight = id`, via `mapPath_inclRight_wallFree` + the shipped faithfulness `mapPath_inclRight_injective`)
— a genuine BIJECTION between monad 1-cells and wall-free pushout 1-cells at the single mode, probed both directions
on the concrete `t·t` (`pathInvert_forward_probe` / `pathInvert_reverse_probe`).  This is the r10 ledger's B1 node,
unblocked by the r11 transport.  It is NOT `wallFreeCellInvert` (the cell-level converse) nor `finestLayout` (the
cell-carrying pairs).  No marker flips.  `= true`. -/
def fxAmalg_hasWallFreePathInversion : Bool := true

end FX1Poly.Polygraph.Amalgam
