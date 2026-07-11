import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestPairs
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalFiringBlockReader

/-! # Polygraph/TwoCategory/Amalgam/PushoutFiringBlockProducer — the COARSE firing-block producer `firingBlockLayout`
(one pair per maximal `t`-run), its by-construction slot-count spec, and its domain / codomain round-trips
(WP-AMALG-2 r19, Brick B2)

r17 (`PushoutCanonicalFiringBlockReader.lean`) named the residual `fxAmalg_firingBlockProducerStaysWalled`: the
GENERAL coarse producer `firingBlockLayout : path → List VcompGapPair` at firing-block granularity — one pair per
maximal `t`-run, `length = wallCount + 1` — contrast the shipped per-letter `finestLayout` whose `length =
path.length`.  This file AUTHORS that producer, mirroring the shipped `finestGapWidthsAux` recursion at PATH
granularity: a `(pendingWall, currentGap)` accumulator, closing the current gap into a block at each `s`-wall,
widening it at each `t`-letter.

## The producer (the tag-walk, mirroring `finestGapWidthsAux`)

`firingBlockLayoutAux pendingWall currentGap` reads the path letter-by-letter (via the r11 transport
`pushoutEndoPathOfWord`):
  * `.nil` — emit the final block `idBlockPair pendingWall currentGap` (the trailing gap).
  * `.cons letter rest`, `letterTag = true` (`s`-wall) — CLOSE the current gap (emit `idBlockPair pendingWall
    currentGap`), then recurse with the wall reset to the `s`-letter and an empty new gap.
  * `.cons letter rest`, `letterTag = false` (`t`-gap) — WIDEN the current gap (`composePath currentGap [letter]`),
    recurse with the same pending wall.
The three arms are IDENTICAL in shape to `finestGapWidthsAux` (each `true` emits one block + recurses, each `false`
recurses with no emit, `[]` emits one), so the slot count is `wallCount + 1` BY CONSTRUCTION.  Each block carries an
IDENTITY 2-cell payload (`idBlockPair`) — the base producer; the `gen` / `id` arms of the total assembly override the
relevant gap payload afterwards.

## The by-construction slot-count spec

`firingBlockLayoutAux_length` proves `(firingBlockLayoutAux pw cg path).length = pushoutPathWallCount path + 1`,
STRUCTURAL, mirroring `finestGapWidthsAux_length` (full-enum `Bool` head, `Nat.zero_add` / `Nat.add_comm`).  Then
`firingBlockLayout_slotCount` gives `(firingBlockLayout path).length = (finestGapWidths (pushoutPathTags path)).length`
— both `wallCount + 1` (via `finestGapWidths_pushoutPathTags_length`), the r17 SPEC met BY CONSTRUCTION.

## The round-trips (via the word reflection, propext-safe)

`gapDomLayout_firingBlockLayout` / `gapCodLayout_firingBlockLayout` (`gapDomLayout nil ∘ firingBlockLayout = id` on
endo paths) go through the WORD level (`firingBlockLayoutAux_domWord` / `_codWord`) and lift by the r11 reflection
`pushoutPathWord_injective`.  The accumulator word invariant `word(gapDomLayout nil (firingBlockLayoutAux pw cg
path)) = word(pw) ++ (word(cg) ++ word(path))` uses the CLEAN `pushoutPathWord_composePath` and a hand-rolled
propext-safe `pushoutWordAppendAssoc` (core `List.append_assoc` DEPENDS ON `propext`) — the ONE reassociation the
gap-widening case needs.

## What STAYS WALLED (no flip)

This ships the coarse producer + the by-construction slot-count spec + the round-trips — the r17-named
`fxAmalg_firingBlockProducerStaysWalled` residual, now flipped to SHIPPED.  It does NOT ship the total canonical
reader (threading each body's own conv), the interior-ordinal `s`-frame producer, or the JAM A per-gap descent.
`fxAmalg_totalCanonicalReaderStaysGated` STAYS `true`; the masters STAY at their walled values; #2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL on the path / word; hand-rolled append-assoc (no core `List.append_assoc`).
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## A propext-safe list-append associativity (core `List.append_assoc` leaks propext) -/

/-- A **propext-safe append associativity** — `(first ++ second) ++ third = first ++ (second ++ third)`, hand-rolled
by structural cons-recursion on `first` (`[]` is `nil_append` `rfl`; `cons` is a `congrArg`).  Core
`List.append_assoc` DEPENDS ON `propext` in this Lean; this reproves it cons-only, propext-free.  The ONE
reassociation the gap-widening round-trip case needs. -/
theorem pushoutWordAppendAssoc {elementType : Type _} :
    (first : List elementType) → (second third : List elementType) →
    (first ++ second) ++ third = first ++ (second ++ third)
  | [], _, _ => rfl
  | head :: rest, second, third => congrArg (head :: ·) (pushoutWordAppendAssoc rest second third)

/-! ## The identity-payload wall/gap block -/

/-- The **identity-payload wall/gap block** — a `VcompGapPair` with leading wall `wall`, a gap whose domain, middle,
and codomain are all the SAME word `gap`, and IDENTITY 2-cell payloads (`id gap` upper and lower).  The base
producer's block: the shape carries the wall and gap words; the payload is inert (overridden per firing region by the
`gen` arm of the total assembly). -/
def idBlockPair {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (wall gap : ModalityPath signature.graph oneMode oneMode) : VcompGapPair signature oneMode where
  wall := wall
  gapDom := gap
  gapMid := gap
  gapCod := gap
  upper := RawTwoCellExpr.id gap
  lower := RawTwoCellExpr.id gap

/-! ## The coarse producer (the tag-walk, mirroring `finestGapWidthsAux`) -/

/-- The **coarse firing-block producer accumulator** — reads a pushout 1-cell letter-by-letter carrying a pending
leading `wall` word and the currently-open `gap` word.  On the empty path it emits the final block; on an `s`-wall
(`letterTag = true`) it CLOSES the current gap (emits `idBlockPair pendingWall currentGap`) and reopens with the
`s`-letter as the new wall and an empty gap; on a `t`-gap (`letterTag = false`) it WIDENS the current gap and
recurses.  Full-enum `bif` on the tag (propext-free); structural on the path (both branches recurse on `rest`).  The
PATH-granularity mirror of `finestGapWidthsAux`, one block per maximal `t`-run (a leading gap, one per wall, a
trailing gap). -/
def firingBlockLayoutAux
    (pendingWall currentGap :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode →
    List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)
  | _, _, .nil _ => [idBlockPair pendingWall currentGap]
  | _, _, .cons letter rest =>
      bif letterTag involutionMonadSplit letter.val then
        idBlockPair pendingWall currentGap ::
          firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest
      else
        firingBlockLayoutAux pendingWall
          (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest

/-- ★★★ **THE COARSE FIRING-BLOCK PRODUCER.**  A pushout 1-cell reads to its list of firing-block `VcompGapPair`s
(one per maximal `t`-run), starting with an empty pending wall and empty current gap.  This is the r17-named residual
`firingBlockLayout : path → List VcompGapPair` at firing-block granularity — the COARSE counterpart of the shipped
per-letter `finestLayout`. -/
def firingBlockLayout {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) :
    List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode) :=
  firingBlockLayoutAux (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) path

/-! ## The by-construction slot-count spec -/

/-- ★★ **THE SLOT COUNT IS `wallCount + 1`** (accumulator form).  `(firingBlockLayoutAux pw cg path).length =
pushoutPathWallCount path + 1`, independent of the accumulators: each `s`-wall opens exactly one new block, each
`t`-gap widens without adding a block, and the tail always emits the trailing block.  STRUCTURAL on the path,
mirroring `finestGapWidthsAux_length`: `.nil` is `rfl`; the `false` (`t`-gap) case the widened-accumulator IH after
`Nat.zero_add`; the `true` (`s`-wall) case the reset-accumulator IH plus one, matched by `Nat.add_comm`. -/
theorem firingBlockLayoutAux_length
    (pendingWall currentGap :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    (firingBlockLayoutAux pendingWall currentGap path).length = pushoutPathWallCount path + 1
  | _, _, .nil _ => rfl
  | _, _, .cons letter rest => by
      show (bif letterTag involutionMonadSplit letter.val then
              idBlockPair pendingWall currentGap ::
                firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
                  (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest
            else
              firingBlockLayoutAux pendingWall
                (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest).length
          = wallBitCount (letterTag involutionMonadSplit letter.val) + pushoutPathWallCount rest + 1
      cases hTag : letterTag involutionMonadSplit letter.val with
      | false =>
          show (firingBlockLayoutAux pendingWall
                  (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest).length
              = 0 + pushoutPathWallCount rest + 1
          rw [Nat.zero_add]
          exact firingBlockLayoutAux_length pendingWall
            (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest
      | true =>
          show (idBlockPair pendingWall currentGap ::
                  firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
                    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest).length
              = 1 + pushoutPathWallCount rest + 1
          rw [List.length_cons,
              firingBlockLayoutAux_length (pushoutEndoPathOfWord [letter.val])
                (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest,
              Nat.add_comm (pushoutPathWallCount rest) 1]

/-- ★★★ **THE COARSE PRODUCER MEETS THE r17 SLOT-COUNT SPEC BY CONSTRUCTION.**  `(firingBlockLayout path).length =
(finestGapWidths (pushoutPathTags path)).length` — both `wallCount + 1`.  Combines `firingBlockLayoutAux_length`
(`= pushoutPathWallCount path + 1`) with the shipped `finestGapWidths_pushoutPathTags_length` (the finest slot count
read off the boundary is also `pushoutPathWallCount path + 1`).  The coarse producer's block count IS the canonical
firing-block slot count. -/
theorem firingBlockLayout_slotCount
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) :
    (firingBlockLayout path).length = (finestGapWidths (pushoutPathTags path)).length := by
  rw [firingBlockLayout, firingBlockLayoutAux_length, finestGapWidths_pushoutPathTags_length]

/-! ## The domain / codomain round-trips (via the word reflection) -/

/-- ★★ **THE DOMAIN-WORD ACCUMULATOR INVARIANT.**  `pushoutPathWord (gapDomLayout nil (firingBlockLayoutAux pw cg
path)) = pushoutPathWord pw ++ (pushoutPathWord cg ++ pushoutPathWord path)` — the layout's domain word is the pending
wall word, then the current gap word, then the remaining path word.  STRUCTURAL on the path: `.nil` folds the two
accumulators by `pushoutPathWord_composePath`; the `false` (`t`-gap) case threads the IH with the widened gap and
reassociates by the propext-safe `pushoutWordAppendAssoc`; the `true` (`s`-wall) case threads the IH with the reset
accumulators.  Every `++` step is `pushoutPathWord_composePath` (clean) or a `::`-definitional reduction; no core
append lemma. -/
theorem firingBlockLayoutAux_domWord
    (pendingWall currentGap :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    pushoutPathWord (gapDomLayout
        (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (firingBlockLayoutAux pendingWall currentGap path))
      = pushoutPathWord pendingWall
          ++ (pushoutPathWord currentGap ++ pushoutPathWord path)
  | _, _, .nil _ => by
      show pushoutPathWord (composePath pendingWall
            (composePath currentGap
              (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)))
          = pushoutPathWord pendingWall
              ++ (pushoutPathWord currentGap
                  ++ pushoutPathWord (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode))
      rw [pushoutPathWord_composePath, pushoutPathWord_composePath]
  | _, _, .cons letter rest => by
      show pushoutPathWord (gapDomLayout
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
            (bif letterTag involutionMonadSplit letter.val then
              idBlockPair pendingWall currentGap ::
                firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
                  (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest
            else
              firingBlockLayoutAux pendingWall
                (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest))
          = pushoutPathWord pendingWall
              ++ (pushoutPathWord currentGap ++ pushoutPathWord (ModalityPath.cons letter rest))
      cases hTag : letterTag involutionMonadSplit letter.val with
      | false =>
          show pushoutPathWord (gapDomLayout
                (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
                (firingBlockLayoutAux pendingWall
                  (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest))
              = pushoutPathWord pendingWall
                  ++ (pushoutPathWord currentGap ++ pushoutPathWord (ModalityPath.cons letter rest))
          rw [firingBlockLayoutAux_domWord pendingWall
                (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest,
              pushoutPathWord_composePath, pushoutPathWord_pushoutEndoPathOfWord]
          exact congrArg (pushoutPathWord pendingWall ++ ·)
            (pushoutWordAppendAssoc (pushoutPathWord currentGap) [letter.val] (pushoutPathWord rest))
      | true =>
          show pushoutPathWord (composePath pendingWall
                (composePath currentGap
                  (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
                    (firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
                      (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest))))
              = pushoutPathWord pendingWall
                  ++ (pushoutPathWord currentGap ++ pushoutPathWord (ModalityPath.cons letter rest))
          rw [pushoutPathWord_composePath, pushoutPathWord_composePath,
              firingBlockLayoutAux_domWord (pushoutEndoPathOfWord [letter.val])
                (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest,
              pushoutPathWord_pushoutEndoPathOfWord]
          rfl

/-- ★★ **THE CODOMAIN-WORD ACCUMULATOR INVARIANT** — the `.gapCod` dual of `firingBlockLayoutAux_domWord`.  Because
every `idBlockPair` has `gapCod = gapDom`, the proof is character-identical with `gapCodLayout` in place of
`gapDomLayout`. -/
theorem firingBlockLayoutAux_codWord
    (pendingWall currentGap :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    pushoutPathWord (gapCodLayout
        (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (firingBlockLayoutAux pendingWall currentGap path))
      = pushoutPathWord pendingWall
          ++ (pushoutPathWord currentGap ++ pushoutPathWord path)
  | _, _, .nil _ => by
      show pushoutPathWord (composePath pendingWall
            (composePath currentGap
              (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)))
          = pushoutPathWord pendingWall
              ++ (pushoutPathWord currentGap
                  ++ pushoutPathWord (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode))
      rw [pushoutPathWord_composePath, pushoutPathWord_composePath]
  | _, _, .cons letter rest => by
      show pushoutPathWord (gapCodLayout
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
            (bif letterTag involutionMonadSplit letter.val then
              idBlockPair pendingWall currentGap ::
                firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
                  (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest
            else
              firingBlockLayoutAux pendingWall
                (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest))
          = pushoutPathWord pendingWall
              ++ (pushoutPathWord currentGap ++ pushoutPathWord (ModalityPath.cons letter rest))
      cases hTag : letterTag involutionMonadSplit letter.val with
      | false =>
          show pushoutPathWord (gapCodLayout
                (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
                (firingBlockLayoutAux pendingWall
                  (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest))
              = pushoutPathWord pendingWall
                  ++ (pushoutPathWord currentGap ++ pushoutPathWord (ModalityPath.cons letter rest))
          rw [firingBlockLayoutAux_codWord pendingWall
                (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest,
              pushoutPathWord_composePath, pushoutPathWord_pushoutEndoPathOfWord]
          exact congrArg (pushoutPathWord pendingWall ++ ·)
            (pushoutWordAppendAssoc (pushoutPathWord currentGap) [letter.val] (pushoutPathWord rest))
      | true =>
          show pushoutPathWord (composePath pendingWall
                (composePath currentGap
                  (gapCodLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
                    (firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
                      (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest))))
              = pushoutPathWord pendingWall
                  ++ (pushoutPathWord currentGap ++ pushoutPathWord (ModalityPath.cons letter rest))
          rw [pushoutPathWord_composePath, pushoutPathWord_composePath,
              firingBlockLayoutAux_codWord (pushoutEndoPathOfWord [letter.val])
                (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest,
              pushoutPathWord_pushoutEndoPathOfWord]
          rfl

/-- ★★ **The domain layout of `firingBlockLayout` reads the original boundary word** — `pushoutPathWord (gapDomLayout
nil (firingBlockLayout path)) = pushoutPathWord path`.  The accumulator invariant `firingBlockLayoutAux_domWord` at
the empty accumulators: `word(nil) ++ (word(nil) ++ word(path)) = word(path)` by two `nil_append` definitional
reductions. -/
theorem pushoutPathWord_firingBlockLayout
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) :
    pushoutPathWord (gapDomLayout
        (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (firingBlockLayout path))
      = pushoutPathWord path :=
  firingBlockLayoutAux_domWord
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) path

/-- ★★★ **THE DOMAIN ROUND-TRIP** — `gapDomLayout nil ∘ firingBlockLayout = id` on endo paths.  The word-level
round-trip (`pushoutPathWord_firingBlockLayout`) lifts to the path level by the r11 reflection
`pushoutPathWord_injective`.  The coarse producer's domain boundary reconstructs the original 1-cell. -/
theorem gapDomLayout_firingBlockLayout
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (firingBlockLayout path)
      = path :=
  pushoutPathWord_injective _ path (pushoutPathWord_firingBlockLayout path)

/-- ★★★ **THE CODOMAIN ROUND-TRIP** — `gapCodLayout nil ∘ firingBlockLayout = id` on endo paths.  Same reflection off
`firingBlockLayoutAux_codWord`; every `idBlockPair` has `gapCod = gapDom`, so the codomain layout equals the domain
layout, both `= path`. -/
theorem gapCodLayout_firingBlockLayout
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    gapCodLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (firingBlockLayout path)
      = path :=
  pushoutPathWord_injective _ path
    (firingBlockLayoutAux_codWord
      (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
      (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) path)

/-! ## The degenerate-path probes (all-wall, all-gap) -/

/-- ★★★ **PROBE (all-wall degenerate path `s·s`) — THREE slots, all empty gaps.**  `(firingBlockLayout
unitSplitsWallDom).length = 3` (`rfl`) — the two `s`-walls read THREE firing-block slots (a leading empty gap, one
per wall, a trailing empty gap), matching `finestGapWidths [s, s] = [0, 0, 0]`.  The all-wall degenerate case: every
block is `idBlockPair (s or nil) nil`. -/
theorem firingBlockLayout_allWall_slotCount :
    (firingBlockLayout unitSplitsWallDom).length = 3 := rfl

/-- ★★★ **PROBE (all-gap degenerate path `t·t`) — ONE slot.**  `(firingBlockLayout (composePath monadPushTPath
monadPushTPath)).length = 1` (`rfl`) — a wall-free (pure-`t`) boundary reads ONE firing-block slot (the whole thing is
one maximal `t`-run), matching `wallCount 0 + 1 = 1`.  The all-gap degenerate case: one block `idBlockPair nil (t·t)`.
-/
theorem firingBlockLayout_allGap_slotCount :
    (firingBlockLayout (composePath monadPushTPath monadPushTPath)).length = 1 := rfl

/-- ★★★ **PROBE (wall-gap-wall `s·t·s`) — THREE slots.**  `(firingBlockLayout unitSplitsWallCod).length = 3` (`rfl`)
— the SAME slot count as the `s·s` domain (the empty-gap admission), the middle gap widened `0 → 1`.  Matches
`finestGapWidths [s, t, s] = [0, 1, 0]`. -/
theorem firingBlockLayout_wallGapWall_slotCount :
    (firingBlockLayout unitSplitsWallCod).length = 3 := rfl

/-- ★★★ **PROBE (the coarse producer's block count = the finest spec, on the r8 wall-splitter).**  On the r8
wall-splitting boundaries, the coarse producer's block count equals the finest spec slot count BY CONSTRUCTION —
`(firingBlockLayout unitSplitsWallDom).length = (finestGapWidths (pushoutPathTags unitSplitsWallDom)).length` — via
the general `firingBlockLayout_slotCount`, the r17 SPEC met on the very cell that refuted the wall-BLOCK skeleton. -/
theorem firingBlockLayout_meetsSpecOnWallSplitter :
    (firingBlockLayout unitSplitsWallDom).length
      = (finestGapWidths (pushoutPathTags unitSplitsWallDom)).length :=
  firingBlockLayout_slotCount unitSplitsWallDom

/-! ## Observability -/

-- The coarse producer's slot counts: all-wall `s·s` (expect `3`), all-gap `t·t` (expect `1`), `s·t·s` (expect `3`).
#eval (firingBlockLayout unitSplitsWallDom).length
#eval (firingBlockLayout (composePath monadPushTPath monadPushTPath)).length
#eval (firingBlockLayout unitSplitsWallCod).length

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the COARSE firing-block PRODUCER `firingBlockLayout` SHIPS (WP-AMALG-2 r19, B2).**
`= true`.  `firingBlockLayoutAux` / `firingBlockLayout` produce one firing-block `VcompGapPair` per maximal `t`-run
(the PATH-granularity mirror of `finestGapWidthsAux`, a `(pendingWall, currentGap)` accumulator closing a block at
each `s`-wall, widening the gap at each `t`-letter, identity payloads).  The slot count is `wallCount + 1` BY
CONSTRUCTION: `firingBlockLayoutAux_length` (`(firingBlockLayoutAux pw cg path).length = pushoutPathWallCount path +
1`, structural, mirroring `finestGapWidthsAux_length`), so `firingBlockLayout_slotCount` MEETS the r17 spec
(`(firingBlockLayout path).length = (finestGapWidths (pushoutPathTags path)).length`).  The domain / codomain
round-trips ship (`gapDomLayout_firingBlockLayout` / `gapCodLayout_firingBlockLayout`, `gapDomLayout nil ∘
firingBlockLayout = id` on endo paths, via the word invariants `firingBlockLayoutAux_domWord` / `_codWord` — using
the clean `pushoutPathWord_composePath` and a propext-safe hand-rolled `pushoutWordAppendAssoc` — lifted by
`pushoutPathWord_injective`).  Probed on the degenerate paths: all-wall `s·s` (`3` slots), all-gap `t·t` (`1` slot),
`s·t·s` (`3` slots), and the coarse count = finest spec on the r8 wall-splitter.

This FLIPS the r17-named residual `fxAmalg_firingBlockProducerStaysWalled` to SHIPPED (recorded by
`firingBlockProducerShipsFlipsResidual` below).  It does NOT ship the total canonical reader (threading each body's
own conv), the interior-ordinal `s`-frame producer, or the JAM A per-gap descent.
`fxAmalg_totalCanonicalReaderStaysGated` STAYS `true`; the masters STAY at their walled values; #2043 does NOT close.
`= true`. -/
def fxAmalg_hasFiringBlockProducer : Bool := true

/-- ★★★ **The r17 firing-block PRODUCER residual node, and the coverage it now has (`rfl`).**  r17 held
`fxAmalg_firingBlockProducerStaysWalled = true` naming the coarse producer over arbitrary paths as deferred
engineering; B2 AUTHORS that producer (`firingBlockLayout`, slot-count spec, round-trips), SUPERSEDING the r17
residual with `fxAmalg_hasFiringBlockProducer`.  The r17 marker's home value is left intact (additive, historical);
this records that node at its shipped-value `true` and confirms the total canonical reader stays gated
(`fxAmalg_firingBlockProducerStaysWalled = true` — the producer ships but the total canonical READER threading it
does not).  Machine-checked. -/
theorem firingBlockProducerShipsFlipsResidual :
    fxAmalg_firingBlockProducerStaysWalled = true := rfl

end FX1Poly.Polygraph.Amalgam
