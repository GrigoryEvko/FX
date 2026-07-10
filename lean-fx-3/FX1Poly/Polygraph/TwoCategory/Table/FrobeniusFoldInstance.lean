import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusReadback

/-! # Polygraph/TwoCategory/Table/FrobeniusFoldInstance — the deep diagram invariant as `rowConvInvariant`
legs on carrier A, with the residual banked precisely (POLY-TAB r1 FROB-RESUME, B2)

B1 (`Table/FrobeniusReadback.lean`) wired the A -> B readback and transported `extraSpiderDiagramOf` onto carrier A
as `frobeniusSpiderInvariant`, resolving POLY-TAB-1 obstruction (1).  This file discharges the `rowConvInvariant`
legs of the DEEP invariant that close, and banks the exact residual.

## What closes (shipped here)

  * **The `rowsPreserve` leg** (`frobeniusSpiderInvariant_rowsPreserve`) — GENERIC over an arbitrary
    `FrobeniusLawRel` row (not per-cell): the four rows are cased and each discharged by the shipped seed
    soundness (`frobeniusSpiderInvariant_{unitLeft,frobLeft,frobRight,special}`).  This is the genuine
    `ofRelation` field of an `IsSaturatedCongruence` / the `rowsPreserve` argument of `rowConvInvariant_foldEq`.
  * **The boundary-unfold lemmas** (`_vcompSplit`, `_whiskerRightBoundary`, `_whiskerLeftBoundary`) — the deep
    invariant on each `RawTwoCellExpr` constructor, in terms of the readback homomorphism + `composePath_length`.
    These are the algebraic shape every context leg reduces to.
  * **The `vcompCongrLeft` context leg** (`frobeniusSpiderInvariant_vcompLeftPreserves`), CONDITIONAL on the two
    genuine B-carrier side conditions (`0 < bottomCount`, `BrauerWordInRange`): closed by routing the deep-invariant
    equality through `spiderConv_complete` -> the shipped uniform suffix congruence `spiderConv_suffixCongruence`
    -> `spiderConv_partitionSound`.  Fired NON-VACUOUSLY on the `frobLeft` fusion whiskered by a subsequent `μ`.

## The residual, banked precisely (obstruction (2) sharpened; (1) resolved, (3) dissolved)

The full `rowConvInvariant_foldEq`/`foldRel` instance needs SIX legs.  The `refl`/`symm`/`trans` legs are free (`Eq`),
`rowsPreserve` closes here, `vcompCongrLeft` closes modulo its side conditions.  The residual is:

  * **`fullPreserves`** (the `ofFull` / `TwoCellConvFull` 13-arm) — its `ofConv` arm embeds the entire separate
    `TwoCellConv` structural-law inductive, so it is itself a nested induction re-expressing the free-2-category
    laws as readback-word identities under `extraSpiderDiagramOf`; not a `rfl`.
  * **The boundary-CHANGING context legs** (`vcompCongrRight` prefix-append at a shifted boundary; the two whisker
    pad legs `prefixPreserves` = LEFT `shiftBrauerWord` pad, `suffixPreserves` = RIGHT boundary extend) — each needs
    a GENERAL `extraSpiderDiagramOf`-level pad congruence, and the shipped B-carrier pad lemmas
    (`processBrauer_{left,right}PadSim`, `processBrauer_viewCongruence`) carry the `0 < bottomCount` reachability
    precondition (`brauerReachable_conditions`), which the fold's NIL-boundary cells (e.g. `η : id ⇒ t`) violate.

So the precise residual is `fullPreserves` (the free-2-cat + whisker-functoriality fragment) plus the `n = 0`
boundary edge of the shipped pad/view congruences.  Obstruction (1) [the word interpreter] is RESOLVED (B1);
obstruction (3) [the `matchingSameComponent` whisker gate + open `relationAgrees`] is DISSOLVED on carrier A — the
carrier-A context closure is `whiskerLeftCongr`/`whiskerRightCongr` with NO gate premise — so it never appears in
these legs; what remains is exactly obstruction (2) sharpened to the two named pieces.

Raw Lean 4 + Init; the closed legs are `cases` + the shipped bridge; no `omega` / `simp`-AC / `native_decide` /
`WellFounded.fix`.  Additive: nothing outside `Table/` is touched.  Per-declaration `#assert_no_axioms` in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

open FX1Poly.Polygraph.Amalgam

/-! ## The `rowsPreserve` leg — generic over the four rows -/

/-- ★ **The `rowsPreserve` leg of the deep `foldEq`/`foldRel`.**  The deep spider invariant is preserved by ANY
`FrobeniusLawRel` row: case on the four rows, each discharged by the shipped seed soundness.  This is the genuine
`ofRelation` field an `IsSaturatedCongruence` for `frobeniusSpiderInvariant` would carry — not per-cell, but for an
arbitrary row. -/
theorem frobeniusSpiderInvariant_rowsPreserve {sourceMode targetMode : FrobeniusMode}
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath}
    (row : FrobeniusLawRel cellAlpha cellBeta) :
    frobeniusSpiderInvariant cellAlpha = frobeniusSpiderInvariant cellBeta := by
  cases row with
  | unitLeft => exact frobeniusSpiderInvariant_unitLeft
  | frobLeft => exact frobeniusSpiderInvariant_frobLeft
  | frobRight => exact frobeniusSpiderInvariant_frobRight
  | special => exact frobeniusSpiderInvariant_special

/-! ## Boundary-unfold lemmas — the deep invariant on each constructor -/

/-- The deep invariant on a vertical composite splits along the readback homomorphism (`readback (vcomp a b) =
readback a ++ readback b`), at the shared bottom boundary. -/
theorem frobeniusSpiderInvariant_vcompSplit {sourceMode targetMode : FrobeniusMode}
    {oneCellF oneCellG oneCellH : ModalityPath frobeniusGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr frobeniusModeSignature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr frobeniusModeSignature oneCellG oneCellH) :
    frobeniusSpiderInvariant (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = extraSpiderDiagramOf oneCellF.length (readbackToWord cellAlpha ++ readbackToWord cellBeta) := rfl

/-- The deep invariant on a right whisker extends the bottom boundary by the suffix 1-cell length (positions
unchanged), via `composePath_length`. -/
theorem frobeniusSpiderInvariant_whiskerRightBoundary {sourceMode middleMode targetMode : FrobeniusMode}
    {oneCellF oneCellG : ModalityPath frobeniusGraph sourceMode middleMode}
    (suffix1Cell : ModalityPath frobeniusGraph middleMode targetMode)
    (body : RawTwoCellExpr frobeniusModeSignature oneCellF oneCellG) :
    frobeniusSpiderInvariant (RawTwoCellExpr.whiskerRight suffix1Cell body)
      = extraSpiderDiagramOf (oneCellF.length + suffix1Cell.length) (readbackToWord body) := by
  show extraSpiderDiagramOf (composePath oneCellF suffix1Cell).length (readbackToWord body)
     = extraSpiderDiagramOf (oneCellF.length + suffix1Cell.length) (readbackToWord body)
  rw [composePath_length]

/-- The deep invariant on a left whisker shifts the readback by the prefix 1-cell length and extends the bottom
boundary by it (LEFT pad), via `composePath_length` + the `shiftBrauerWord` readback. -/
theorem frobeniusSpiderInvariant_whiskerLeftBoundary {sourceMode middleMode targetMode : FrobeniusMode}
    (prefix1Cell : ModalityPath frobeniusGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath frobeniusGraph middleMode targetMode}
    (body : RawTwoCellExpr frobeniusModeSignature oneCellG oneCellH) :
    frobeniusSpiderInvariant (RawTwoCellExpr.whiskerLeft prefix1Cell body)
      = extraSpiderDiagramOf (prefix1Cell.length + oneCellG.length)
          (shiftBrauerWord prefix1Cell.length (readbackToWord body)) := by
  show extraSpiderDiagramOf (composePath prefix1Cell oneCellG).length
        (shiftBrauerWord prefix1Cell.length (readbackToWord body))
     = extraSpiderDiagramOf (prefix1Cell.length + oneCellG.length)
        (shiftBrauerWord prefix1Cell.length (readbackToWord body))
  rw [composePath_length]

/-! ## The `vcompCongrLeft` context leg — closed via the shipped uniform suffix congruence

Conditional on the two genuine B-carrier side conditions (`0 < bottomCount` and `BrauerWordInRange`).  These are
exactly the preconditions of the shipped `spiderConv_suffixCongruence`; the `0 < bottomCount` one is the `n = 0`
boundary edge banked in the header. -/

/-- ★ **The `vcompCongrLeft` (left-factor congruence) leg of the deep `foldEq`, CONDITIONAL.**  If the left factors
have equal deep invariant, then vcomposing a common right factor preserves it — provided the bottom boundary is
non-empty and the right factor's readback fits (the two shipped-suffix-congruence side conditions).  Routed
`spiderConv_complete` -> `spiderConv_suffixCongruence` -> `spiderConv_partitionSound`, so the whole equality lands
through the shipped uniform suffix congruence with no new B-carrier machinery. -/
theorem frobeniusSpiderInvariant_vcompLeftPreserves {sourceMode targetMode : FrobeniusMode}
    {oneCellF oneCellG oneCellH : ModalityPath frobeniusGraph sourceMode targetMode}
    {cellAlpha cellAlpha' : RawTwoCellExpr frobeniusModeSignature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr frobeniusModeSignature oneCellG oneCellH)
    (bottomPos : 0 < oneCellF.length)
    (suffixInRange : BrauerWordInRange
      (processBrauer (brauerSeed oneCellF.length) (readbackToWord cellAlpha)).openWires.length
      (readbackToWord cellBeta))
    (invariantAgrees : frobeniusSpiderInvariant cellAlpha = frobeniusSpiderInvariant cellAlpha') :
    frobeniusSpiderInvariant (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = frobeniusSpiderInvariant (RawTwoCellExpr.vcomp cellAlpha' cellBeta) :=
  spiderConv_partitionSound
    (spiderConv_suffixCongruence bottomPos (spiderConv_complete invariantAgrees) suffixInRange)

/-! ## Non-vacuity — the closed legs fire on real rows -/

/-- ★ **`rowsPreserve` fires on a real fusion row** — the `frobLeft` row through the generic leg. -/
theorem frobeniusSpiderInvariant_rowsPreserve_frobLeft :
    frobeniusSpiderInvariant frobeniusLeftLhsCell = frobeniusSpiderInvariant frobeniusHCell :=
  frobeniusSpiderInvariant_rowsPreserve FrobeniusLawRel.frobLeft

/-- The `μ` suffix `[multAt 0]` is in range on the two produced strands of `frobeniusLeftLhsCell` (the boundary the
readback of the "S=X" left composite leaves — top count `2`): a single `multAt 0` firing at position `0` inside the
`2`-wide boundary, with no strands to the right (`rightLen = 0`) and the tail empty at its cod boundary `1`. -/
private theorem inRange_frobLeft_mult :
    BrauerWordInRange
      (processBrauer (brauerSeed frobeniusTThenT.length) (readbackToWord frobeniusLeftLhsCell)).openWires.length
      (readbackToWord frobeniusMultCell) :=
  BrauerWordInRange.cons (multAt 0) 0 (by decide) (by decide) (BrauerWordInRange.nil _)

/-- ★ **The `vcompCongrLeft` leg fires NON-VACUOUSLY** — the Frobenius "S=X" fusion `frobeniusLeftLhsCell ~
frobeniusHCell` (equal deep invariant by `frobLeft`) whiskered on the LEFT by a subsequent multiplication `μ` stays
deep-invariant-equal, discharging the `0 < bottomCount` side condition by `decide` and the `BrauerWordInRange` datum
by the explicit firing witness `inRange_frobLeft_mult`.  A genuine in-context compositional identity produced by the
shipped suffix congruence, not a seed row. -/
theorem frobeniusSpiderInvariant_vcompLeft_fires :
    frobeniusSpiderInvariant (RawTwoCellExpr.vcomp frobeniusLeftLhsCell frobeniusMultCell)
      = frobeniusSpiderInvariant (RawTwoCellExpr.vcomp frobeniusHCell frobeniusMultCell) :=
  frobeniusSpiderInvariant_vcompLeftPreserves frobeniusMultCell (by decide) inRange_frobLeft_mult
    frobeniusSpiderInvariant_frobLeft

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the deep-invariant `rowsPreserve` + `vcompCongrLeft` legs SHIP (FROB-RESUME B2).**  The
generic-row `rowsPreserve` leg (`frobeniusSpiderInvariant_rowsPreserve`, all four `FrobeniusLawRel` rows discharged
by the shipped seed soundness) and the `vcompCongrLeft` context leg (`frobeniusSpiderInvariant_vcompLeftPreserves`,
conditional on `0 < bottomCount` + `BrauerWordInRange`, routed through the shipped uniform suffix congruence) are
shipped, with the boundary-unfold lemmas (`_vcompSplit` / `_whiskerRightBoundary` / `_whiskerLeftBoundary`) and a
non-vacuous firing on the `frobLeft` fusion whiskered by `μ` (`frobeniusSpiderInvariant_vcompLeft_fires`).  `= true`. -/
def fxTab_hasDeepDiagramFoldLegs : Bool := true

/-- ★ **Honesty marker — the FULL deep `rowConvInvariant_foldEq`/`foldRel` instance is BANKED precisely (FROB-RESUME
B2 residual).**  Of the six legs: `refl`/`symm`/`trans` are free (`Eq`), `rowsPreserve` ships
(`frobeniusSpiderInvariant_rowsPreserve`), `vcompCongrLeft` ships modulo its two side conditions
(`frobeniusSpiderInvariant_vcompLeftPreserves`).  The RESIDUAL is exactly obstruction (2) sharpened: (a)
`fullPreserves` — the `TwoCellConvFull` 13-arm whose `ofConv` embeds the whole `TwoCellConv` structural inductive, a
nested induction re-expressing the free-2-category laws as `extraSpiderDiagramOf`-word identities; and (b) the
boundary-CHANGING legs (`vcompCongrRight` prefix-append; the two whisker pad legs) which need a GENERAL
`extraSpiderDiagramOf`-level pad congruence, blocked at the NIL-boundary (`n = 0`) cells (e.g. `η : id ⇒ t`) by the
`0 < bottomCount` reachability precondition of the shipped pad/view congruences.  Obstruction (1) [the word
interpreter] is RESOLVED (B1 readback); obstruction (3) [the `matchingSameComponent` whisker gate + open
`relationAgrees`] is DISSOLVED on carrier A (its context closure is gate-free `whiskerLeftCongr`/`whiskerRightCongr`),
so it never appears in these legs.  `= false` until `fullPreserves` + the `n = 0` pad edge land. -/
def fxTab_hasDeepDiagramFoldInstance : Bool := false

end FX1Poly.Polygraph
