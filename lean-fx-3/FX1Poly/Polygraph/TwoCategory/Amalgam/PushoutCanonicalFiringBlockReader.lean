import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalReaderConsistency
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallCountInvariance
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestLayout

/-! # Polygraph/TwoCategory/Amalgam/PushoutCanonicalFiringBlockReader — the canonical firing-block SLOT-COUNT SPEC, the
`id`-case canonical upgrade, and the GENERAL dom↔cod slot-count invariant (WP-AMALG-2 r17, Brick B4)

The r17 recon named the canonical reader's slot-count SPEC — `pairs.length = (finestGapWidths (pushoutPathTags A)).length`
— and its two load-bearing facts: (1) `finestGapWidths`'s length is `wallCount + 1` (the wall-count invariant made a
slot count), and (2) that length is a dom↔cod invariant (off `wallLetterCount_dom_eq_cod`).  It also named
(self-attack #4/#5) the `id`-case DEFECT: `pushoutFactorizeId` emits the EMPTY layout (slot count `0`), but
`finestGapWidths []` has length `1` (`finestGapWidthsAux_nonempty`: always ≥ 1, the trailing gap) — so the `id` case is
NON-canonical and must be UPGRADED.  This file authors the SPEC backbone, the general slot invariant, and the
`id nil` canonical upgrade, and PINS the spec per cell class by `rfl` probes.

## The SPEC backbone (the wall-count = slot-count law, general)

  * **`wallTagCount`** — the number of `s`-walls (`true` tags) in a tag sequence.
  * **`finestGapWidthsAux_length` / `finestGapWidths_length`** — `(finestGapWidths tags).length = wallTagCount tags + 1`,
    STRUCTURAL, term-mode (propext-free): the finest slot count is exactly `wallCount + 1`.
  * **`wallTagCount_pushoutPathTags`** — the tag-wall count equals the path wall count `pushoutPathWallCount`.
  * **`finestGapWidths_pushoutPathTags_length`** — `(finestGapWidths (pushoutPathTags path)).length
    = pushoutPathWallCount path + 1`: the SPEC slot count read off any boundary path is `wallCount + 1`.

## The GENERAL dom↔cod slot-count invariant (the skeleton reflection, strengthened)

  * **`finestGapWidths_slotCount_domCod_eq`** — for ANY pushout 2-cell, the domain and codomain read the SAME canonical
    slot count.  A one-line corollary of `finestGapWidths_pushoutPathTags_length` + `wallLetterCount_dom_eq_cod` (the
    wall count is a hard dom↔cod invariant).  This LIFTS the r9 concrete `unitSplitsWall_finestSlotCount_domCod_eq`
    (computed on the two width lists) to a GENERAL cell-level theorem — the "skeleton reflects" half of the JAM A
    narrowing, now off the general wall-count invariant, not a per-path computation.

## The `id`-case canonical upgrade (self-attack #4 fix)

  * **`pushoutFactorizeIdCanonicalNil`** — `id nil` factors as the ONE-slot layout `[emptyGapPair nil]` (a trailing
    width-0 gap), NOT the empty layout: `finalWall = nil`, `pairs = [emptyGapPair nil]`, `rfl` boundary casts, conv by
    `emptyGapLayout_conv_id`.  This is canonical: `pairs.length = 1 = (finestGapWidths (pushoutPathTags nil)).length`
    (`idCanonicalNilSlotCount`, `rfl`) — matching `finestGapWidthsAux_nonempty`'s always-≥-1, unlike `pushoutFactorizeId`
    (slot count `0`).

## What STAYS WALLED (no flip)

This ships the SPEC backbone + the general slot invariant + the `id nil` canonical upgrade + the per-class `rfl` probes.
It does NOT ship the general firing-block PRODUCER over ARBITRARY paths (`firingBlockLayout : path → List VcompGapPair`
at firing-block granularity, with `length = wallCount + 1` and the all-identity conv) — that coarse producer + its
multi-slot all-identity convertibility is the named residual — NOR the `s`-bearing frame's downstream wall-SHIFT (the
wire-changing case, leg 2a'', B2).  Even a COMPLETE canonical reader flips at most `fxAmalg_topFactorizationInductionStaysWalled`
(gated on the wall-shift + wiring); the masters `fxAmalg_hasFullSaturatedPushoutDispatch` /
`fxAmalg_hasGeneralPushoutDispatch` are gated on the JAM A per-gap DESCENT the reader does NOT supply.  #2043 does NOT
close.

Raw Lean 4 + Init.  STRUCTURAL / `rfl` / term-mode.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The SPEC backbone — the wall-count = slot-count law -/

/-- The **wall count of a tag sequence** — the number of `s`-wall (`true`) tags.  Full-enum `Bool` head
(propext-free), structural on the list. -/
def wallTagCount : List Bool → Nat
  | [] => 0
  | true :: rest => wallTagCount rest + 1
  | false :: rest => wallTagCount rest

/-- ★★ **THE FINEST SLOT COUNT IS `wallCount + 1`** (accumulator form).  `(finestGapWidthsAux currentGap tags).length
= wallTagCount tags + 1`, independent of the running gap width `currentGap`: each `true` opens exactly one new slot,
each `false` widens the current slot without adding one, and the tail always emits the trailing slot.  STRUCTURAL on
`tags`, term-mode (propext-free): the `[]` case is `rfl` (`[currentGap]` has length `1`); the `true` case a `congrArg
(· + 1)` on the reset-accumulator IH; the `false` case the widened-accumulator IH directly. -/
theorem finestGapWidthsAux_length :
    (currentGap : Nat) → (tags : List Bool) →
    (finestGapWidthsAux currentGap tags).length = wallTagCount tags + 1
  | _, [] => rfl
  | _, true :: rest => congrArg (· + 1) (finestGapWidthsAux_length 0 rest)
  | currentGap, false :: rest => finestGapWidthsAux_length (currentGap + 1) rest

/-- ★★ **THE FINEST SLOT COUNT SPEC** — `(finestGapWidths tags).length = wallTagCount tags + 1`.  The wall-count
invariant made a slot count: the canonical layout has exactly `wallCount + 1` firing-block slots (a leading gap, one
per wall, a trailing gap). -/
theorem finestGapWidths_length (tags : List Bool) :
    (finestGapWidths tags).length = wallTagCount tags + 1 :=
  finestGapWidthsAux_length 0 tags

/-- ★★ **THE TAG-WALL COUNT EQUALS THE PATH WALL COUNT.**  `wallTagCount (pushoutPathTags path) = pushoutPathWallCount
path` — the number of `true` tags read off the boundary word equals the path's `s`-generator count.  STRUCTURAL on the
path; each `cons` letter's tag is cased (full-enum `Bool`), the `false` case absorbed by `Nat.zero_add`, the `true`
case matched by `Nat.add_comm` against `wallBitCount true = 1`. -/
theorem wallTagCount_pushoutPathTags :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    wallTagCount (pushoutPathTags path) = pushoutPathWallCount path
  | _, _, .nil _ => rfl
  | _, _, .cons letter rest => by
      show wallTagCount (letterTag involutionMonadSplit letter.val :: pushoutPathTags rest)
          = wallBitCount (letterTag involutionMonadSplit letter.val) + pushoutPathWallCount rest
      cases h : letterTag involutionMonadSplit letter.val with
      | false =>
          show wallTagCount (pushoutPathTags rest) = 0 + pushoutPathWallCount rest
          rw [Nat.zero_add]
          exact wallTagCount_pushoutPathTags rest
      | true =>
          show wallTagCount (pushoutPathTags rest) + 1 = 1 + pushoutPathWallCount rest
          rw [wallTagCount_pushoutPathTags rest, Nat.add_comm]

/-- ★★★ **THE SPEC SLOT COUNT OF A BOUNDARY PATH** — `(finestGapWidths (pushoutPathTags path)).length
= pushoutPathWallCount path + 1`.  The canonical firing-block slot count read off any boundary 1-cell is exactly its
wall count plus one.  Combines the finest slot-count law (`finestGapWidths_length`) with the tag-to-path wall count
bridge (`wallTagCount_pushoutPathTags`). -/
theorem finestGapWidths_pushoutPathTags_length
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) :
    (finestGapWidths (pushoutPathTags path)).length = pushoutPathWallCount path + 1 := by
  rw [finestGapWidths_length, wallTagCount_pushoutPathTags]

/-! ## The GENERAL dom↔cod slot-count invariant -/

/-- ★★★ **THE CANONICAL SLOT COUNT IS A dom↔cod INVARIANT (GENERAL).**  For ANY pushout 2-cell, its domain and
codomain read the SAME canonical firing-block slot count: `(finestGapWidths (pushoutPathTags sourcePath)).length
= (finestGapWidths (pushoutPathTags targetPath)).length`.  A one-line corollary — both counts are `wallCount + 1`
(`finestGapWidths_pushoutPathTags_length`), and the wall count is a hard dom↔cod invariant
(`wallLetterCount_dom_eq_cod`, no generator straddles a wall).  This LIFTS the r9 concrete
`unitSplitsWall_finestSlotCount_domCod_eq` (computed on the two width lists `[0,0,0]` / `[0,1,0]`) to a GENERAL
cell-level theorem: the "the canonical reader's dom and cod slot counts agree" fact of the JAM A skeleton reflection,
now off the general wall-count invariant rather than a per-path width computation. -/
theorem finestGapWidths_slotCount_domCod_eq
    {sourceMode targetMode : involutionMonadPushout.toModeSignature.graph.Mode}
    {sourcePath targetPath :
      ModalityPath involutionMonadPushout.toModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath) :
    (finestGapWidths (pushoutPathTags sourcePath)).length
      = (finestGapWidths (pushoutPathTags targetPath)).length := by
  rw [finestGapWidths_pushoutPathTags_length, finestGapWidths_pushoutPathTags_length,
      wallLetterCount_dom_eq_cod cell]

/-! ## The `id`-case canonical upgrade (self-attack #4 fix) -/

/-- ★★★ **THE CANONICAL `id nil` FACTORIZATION.**  `id nil` factors as the ONE-slot layout `[emptyGapPair nil]` (a
single trailing width-0 gap), NOT the empty layout of `pushoutFactorizeId`.  `finalWall = nil`, `pairs = [emptyGapPair
nil]`, boundary casts `rfl` (`gapDomLayout nil [emptyGapPair nil] = nil` on the nose), conv by
`emptyGapLayout_conv_id` (the empty gap collapses to the identity).  This is the CANONICAL convention — the slot count
is `1`, matching `finestGapWidthsAux_nonempty`'s always-≥-1 (`finestGapWidths []` = `[0]`, one trailing slot) — the
self-attack #4 defect fix.  Generic over signature / base relation / single mode. -/
def pushoutFactorizeIdCanonicalNil {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode} :
    PushoutLayoutFactorization baseRel
      (RawTwoCellExpr.id (ModalityPath.nil (graph := signature.graph) oneMode)) where
  finalWall := ModalityPath.nil (graph := signature.graph) oneMode
  pairs := [emptyGapPair (ModalityPath.nil (graph := signature.graph) oneMode)]
  domEq := rfl
  codEq := rfl
  conv := SaturatedConvOver.symm
    (emptyGapLayout_conv_id (ModalityPath.nil (graph := signature.graph) oneMode)
      (ModalityPath.nil (graph := signature.graph) oneMode))

/-! ## The slot-count spec, PINNED per cell class (rfl probes) -/

/-- ★★★ **PROBE — the `id nil` canonical factorization MEETS THE SPEC.**  `(pushoutFactorizeIdCanonicalNil …).pairs.length
= (finestGapWidths (pushoutPathTags nil)).length` — both `1`, by `rfl`.  The `id`-case now satisfies the canonical
slot-count spec (contrast `pushoutFactorizeId`, whose empty layout gives `0 ≠ 1`). -/
theorem idCanonicalNilSlotCount :
    (pushoutFactorizeIdCanonicalNil (signature := involutionMonadPushout.toModeSignature)
        crossPairRealPushoutRel (oneMode := monadPushMode)).pairs.length
      = (finestGapWidths (pushoutPathTags
          (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode))).length :=
  rfl

/-- ★★ **PROBE (0-wall cell class, `id nil`) — 1 slot.**  `(finestGapWidths []).length = 1`: a wall-free boundary reads
ONE canonical slot (the trailing gap).  Pins the spec for the wall-free / `gen` / `id nil` class. -/
theorem finestSlotCount_wallFree : (finestGapWidths ([] : List Bool)).length = 1 := rfl

/-- ★★ **PROBE (2-wall cell class, `s·s` domain) — 3 slots.**  `(finestGapWidths [s, s]).length = 3` = `wallCount 2 +
1`: two walls read THREE canonical slots (leading, middle, trailing gaps). -/
theorem finestSlotCount_wallWall : (finestGapWidths [true, true]).length = 3 := rfl

/-- ★★ **PROBE (2-wall cell class, `s·t·s` codomain) — 3 slots.**  `(finestGapWidths [s, t, s]).length = 3` — the SAME
slot count as the `s·s` domain (`finestSlotCount_wallWall`), the middle gap merely widening `0 → 1`.  The empty-gap
admission pinned at firing-block granularity. -/
theorem finestSlotCount_wallGapWall : (finestGapWidths [true, false, true]).length = 3 := rfl

/-- ★★★ **PROBE (the general dom↔cod invariant FIRES on the r8 wall-splitter).**  The wire-creating `unitSplitsWallCell`
(`s·s ⇒ s·t·s`, whose wall-BLOCK list splits, r8) has its domain and codomain canonical slot counts AGREE (both `3`),
derived from the GENERAL `finestGapWidths_slotCount_domCod_eq` off `wallLetterCount_dom_eq_cod` — not the r9 per-path
width computation.  The skeleton reflection, machine-witnessed on the very cell that refuted the wall-block skeleton. -/
theorem unitSplitsWallCanonicalSlotCountAgrees :
    (finestGapWidths (pushoutPathTags unitSplitsWallDom)).length
      = (finestGapWidths (pushoutPathTags unitSplitsWallCod)).length :=
  finestGapWidths_slotCount_domCod_eq unitSplitsWallCell

/-! ## Observability -/

-- The canonical `id nil` slot count (expect `1`: the trailing gap, NOT the empty layout's `0`).
#eval (pushoutFactorizeIdCanonicalNil (signature := involutionMonadPushout.toModeSignature)
    crossPairRealPushoutRel (oneMode := monadPushMode)).pairs.length
-- The spec slot count of `s·t·s` (expect `3`).
#eval (finestGapWidths (pushoutPathTags unitSplitsWallCod)).length

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the canonical firing-block SLOT-COUNT SPEC + the `id`-case upgrade SHIP (WP-AMALG-2 r17,
B4).**  `= true`.  The SPEC backbone ships: `finestGapWidths_length` (`(finestGapWidths tags).length = wallTagCount tags
+ 1`, structural term-mode), `wallTagCount_pushoutPathTags` (tag-wall count = path wall count), and
`finestGapWidths_pushoutPathTags_length` (`(finestGapWidths (pushoutPathTags path)).length = pushoutPathWallCount path +
1`) — the canonical slot count read off any boundary is `wallCount + 1`.  The GENERAL dom↔cod invariant
`finestGapWidths_slotCount_domCod_eq` (ANY cell's domain / codomain read the SAME canonical slot count, off
`wallLetterCount_dom_eq_cod`) LIFTS the r9 concrete admission to a cell-level theorem.  The self-attack #4 defect is
fixed: `pushoutFactorizeIdCanonicalNil` factors `id nil` as the ONE-slot `[emptyGapPair nil]` (NOT the empty layout),
meeting the spec (`idCanonicalNilSlotCount`, `pairs.length = 1 = (finestGapWidths (pushoutPathTags nil)).length`, `rfl`).
The spec is PINNED per cell class by `rfl` probes: `finestSlotCount_wallFree` (`1`), `finestSlotCount_wallWall` (`3`),
`finestSlotCount_wallGapWall` (`3`), and the invariant FIRES on the r8 wall-splitter
(`unitSplitsWallCanonicalSlotCountAgrees`, both `3`).

This does NOT ship the general firing-block PRODUCER over arbitrary paths (the coarse `firingBlockLayout` with its
multi-slot all-identity conv) or the `s`-frame downstream wall-SHIFT (the wire-changing case, leg 2a'').  #2043 does NOT
close.  No fabricated flip.  `= true`. -/
def fxAmalg_hasCanonicalFiringBlockSlotSpec : Bool := true

/-- ★★★ **JAM A RE-AUDIT (STRENGTHENED skeleton reflection; per-gap descent STILL the residual) — WP-AMALG-2 r17, B4.**
`= true` (the honest re-audit, no flip).  The r16 JAM A narrowing (`reconR16JamANarrowed`: skeleton reflects, per-gap
descent open) is re-audited with the r17 slot-count spec in hand.  The "skeleton reflects" half is now STRENGTHENED
from the r9 per-path width computation to the GENERAL cell-level `finestGapWidths_slotCount_domCod_eq` (the canonical
slot count is a dom↔cod invariant for ANY cell, off `wallLetterCount_dom_eq_cod`).  The per-gap DESCENT half —
"conv-of-images ⟹ per-gap-conv" (the convex-block projection sound only for word-preserving presentations, which the
wire-creating `eta` : `t^0 ⇒ t` / `mu` : `t^2 ⇒ t` VIOLATE, changing gap WIDTHS `0 → 1` / `2 → 1` exactly where the
precondition fails) — STAYS the residual: `fxAmalg_hasSaturatedDispatchTheorem` STAYS `false`.  So even the r17
slot-count spec does NOT supply the descent.  The masters STAY: `fxAmalg_hasFullSaturatedPushoutDispatch` /
`fxAmalg_hasGeneralPushoutDispatch` `false`, `fxAmalg_topFactorizationInductionStaysWalled` `true`.  Named node: the
per-gap descent (the signature-specific soundness lemma), coupled to the `s`-frame wall-shift (B2 leg 2a'') and the
WalkingMonad reconstruction iso (fib-3, READ-ONLY).  #2043 does NOT close.  No descent overclaim.  `= true`. -/
def fxAmalg_canonicalReaderJamANarrowed : Bool := true

/-- ★★ **Honesty marker — the general firing-block PRODUCER over arbitrary paths STAYS the named residual (WP-AMALG-2
r17, B4).**  `= true` (the wall is honestly held).  This file ships the canonical slot-count SPEC and the `id nil`
canonical factorization, but the GENERAL coarse producer `firingBlockLayout : path → List VcompGapPair` at firing-block
granularity (one pair per maximal `t`-run, `length = wallCount + 1`, contrast the shipped per-letter `finestLayout`
whose `length = path.length`) — together with its multi-slot all-identity convertibility `gapVcompLayout nil
(firingBlockLayout path) ≈ id path` for the general `id`-case — is the deferred engineering.  The width-level SPEC
(`finestGapWidths_pushoutPathTags_length`) and the concrete `id nil` producer ship; the arbitrary-path coarse producer
does not.  `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close.  `= true`. -/
def fxAmalg_firingBlockProducerStaysWalled : Bool := true

end FX1Poly.Polygraph.Amalgam
