import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutNormalForm
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordMultGen

/-! # Polygraph/TwoCategory/Amalgam/PushoutShiftedGapSplice — the WIRE-CHANGING (shifted) forward splice: a
horizontal wall/gap layout whose gaps change the wire count and shift the walls (WP-AMALG-2 r6, B2)

`PushoutMultiGapFactorization.lean` (r5) shipped `multiGapEndoSplice`: the ARBITRARY-arity forward splice at a
FIXED wire count — every gap an ENDOMORPHISM `t^k ⇒ t^k` on ONE shared boundary, spliced by a VERTICAL vcomp fold.
This file GENERALIZES it to WIRE-CHANGING gaps `t^a ⇒ t^b` (`a ≠ b`, a genuine `mu`/`eta` firing), where the
`s`-walls SHIFT dom-to-cod and the layout is a HORIZONTAL composite, NOT a vertical fold on a shared boundary.

## The shift, absorbed by the horizontal composite (no cast-chasing)

B1 (`PushoutWallCountInvariance.lean`) proved the walls are CONSERVED (never consumed) but SHIFT deterministically:
a gap `t^a ⇒ t^b` moves the walls to its right by `b − a`.  The endo splice sidesteps the shift (fixed boundary,
vcomp fold); the wire-changing splice CANNOT — dom and cod differ.  The clean carrier is the HORIZONTAL composite
`s ▷ gap₀ ⊙ s ▷ gap₁ ⊙ … ⊙ s ▷ gapₙ`: `RawTwoCellExpr.hcomp` already threads the boundary composition
(`hcomp a b : a.dom · b.dom ⇒ a.cod · b.cod`), so the wall SHIFT is absorbed by `hcomp`'s definitional boundary —
NO explicit `castBoundary` obligation survives.  The per-gap fill is threaded by the ALREADY-SHIPPED one-sided
horizontal congruences `SaturatedConvOver.hcompCongrLeft` / `hcompCongrRight` (`WalkingMonad/MonadWordMultGen`).

## What ships (each zero-axiom, STRUCTURAL on the gap list, ASCII-only)

  * **`ShiftedGapFill`** — a per-gap collapse between two PARALLEL cells `gapDom ⇒ gapCod` (the boundaries PACKED as
    fields, so `gapDom ≠ gapCod` is allowed — the wire-changing generalization of `EndoGapFill`, which forces
    `boundary ⇒ boundary`).
  * **`SaturatedConvOver.hcompCongr`** — the TWO-sided horizontal congruence, `trans (hcompCongrLeft …)
    (hcompCongrRight …)` of the two shipped one-sided congruences.
  * **`shiftedGapDom` / `shiftedGapCod` / `shiftedGapSourceCell` / `shiftedGapTargetCell`** — the wall/gap layout as
    a right-nested horizontal composite (a wall `s` before each gap), source (presented) vs target (normalized).
  * **`multiGapShiftedSplice`** — THE WIRE-CHANGING FORWARD SPLICE: the source layout is saturated-convertible to
    the target layout, structural on the gap list by `hcompCongr` threading each gap's `fill` and `refl` on the
    inert `s`-walls.  Over ANY signature and base relation.
  * **`shiftedTwoGapSpliceWitness`** — non-vacuity on a genuinely WIRE-CHANGING, TWO-`s`-wall word: `s·(t·t·t)·s·t`
    (a `mu`-associativity gap `t^3 ⇒ t` — the wall to its right SHIFTS by 2 — plus an endo left-unit gap `t ⇒ t`),
    both per-gap fills the shipped right-image collapses (`pushoutAssocGapConv` / `pushoutLeftUnitGapConv`),
    normalized END-TO-END across the two `s`-walls.

The per-gap collapse routes through the shipped two-sided decision (`pushoutRightImageTwoSidedDecision` takes
ARBITRARY reconstructed cells, wire-changing included), so wire-changing per-gap fills are FREE.  The full
arbitrary-word Decidable still needs the CONVERSE (an arbitrary cell FACTORS into this shifted-gap form) — the
completeness residual named in `PushoutWireChangeLedger.lean`.  #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The two-sided horizontal congruence -/

/-- ★ **The two-sided horizontal congruence** for the generic saturated conv — threading a convertibility through
BOTH factors of a horizontal composite: `trans` of the two shipped one-sided congruences
(`SaturatedConvOver.hcompCongrLeft` on the left factor, then `hcompCongrRight` on the right).  Since a
`SaturatedConvOver` relates PARALLEL cells, `cellAlpha'` shares `cellAlpha`'s codomain, so the right-factor
whiskering is well-typed on both. -/
theorem SaturatedConvOver.hcompCongr {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath signature.graph middleMode targetMode}
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellFDom oneCellFCod}
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellGDom oneCellGCod}
    (convAlpha : SaturatedConvOver signature baseRel cellAlpha cellAlpha')
    (convBeta : SaturatedConvOver signature baseRel cellBeta cellBeta') :
    SaturatedConvOver signature baseRel (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      (RawTwoCellExpr.hcomp cellAlpha' cellBeta') :=
  SaturatedConvOver.trans (SaturatedConvOver.hcompCongrLeft convAlpha cellBeta)
    (SaturatedConvOver.hcompCongrRight cellAlpha' convBeta)

/-! ## The wire-changing gap fill and the horizontal wall/gap layout -/

/-- A **wire-changing gap fill** — a saturated convertibility between two PARALLEL cells `gapDom ⇒ gapCod` (the
boundaries PACKED as fields, so `gapDom ≠ gapCod` is allowed): the gap's presented content `source` and its normal
form `target`, both realizing the SAME wire-change `gapDom ⇒ gapCod`, made convertible by `fill`.  The
wire-changing generalization of `EndoGapFill` (which pins `gapDom = gapCod = boundary`).  All boundaries are
endo-1-cells at a single mode `oneMode` (matching the involution+monad pushout, `modeCount = 1`), so a list of them
composes horizontally. -/
structure ShiftedGapFill (signature : ModeSignature) (baseRel : CellRel signature)
    (oneMode : signature.graph.Mode) : Type where
  /-- The gap's domain 1-cell (`t^a`). -/
  gapDom : ModalityPath signature.graph oneMode oneMode
  /-- The gap's codomain 1-cell (`t^b`, possibly `a ≠ b`). -/
  gapCod : ModalityPath signature.graph oneMode oneMode
  /-- The gap's presented content. -/
  source : RawTwoCellExpr signature gapDom gapCod
  /-- The gap's normal form. -/
  target : RawTwoCellExpr signature gapDom gapCod
  /-- The per-gap convertibility (a wire-changing right-image collapse). -/
  fill : SaturatedConvOver signature baseRel source target

/-- The **domain layout** of a wall/gap list — the right-nested horizontal composite `wall · gap₀.dom · wall ·
gap₁.dom · … ` (a wall `s` before each gap).  Structural on the list; the empty layout is the identity 1-cell. -/
def shiftedGapDom {signature : ModeSignature} {baseRel : CellRel signature} {oneMode : signature.graph.Mode}
    (wall : ModalityPath signature.graph oneMode oneMode) :
    List (ShiftedGapFill signature baseRel oneMode) → ModalityPath signature.graph oneMode oneMode
  | [] => identityPath oneMode
  | gap :: rest => composePath wall (composePath gap.gapDom (shiftedGapDom wall rest))

/-- The **codomain layout** of a wall/gap list — the same right-nested horizontal composite with each gap's
CODOMAIN.  The walls sit at the SHIFTED absolute positions (each gap `t^a ⇒ t^b` moves the walls to its right by
`b − a`). -/
def shiftedGapCod {signature : ModeSignature} {baseRel : CellRel signature} {oneMode : signature.graph.Mode}
    (wall : ModalityPath signature.graph oneMode oneMode) :
    List (ShiftedGapFill signature baseRel oneMode) → ModalityPath signature.graph oneMode oneMode
  | [] => identityPath oneMode
  | gap :: rest => composePath wall (composePath gap.gapCod (shiftedGapCod wall rest))

/-- The **source layout CELL** — the presented wall/gap cell as a horizontal composite: each inert wall `s` (an
identity 2-cell) horizontally composed with each gap's presented `source`.  Its boundary is `shiftedGapDom ⇒
shiftedGapCod`.  Structural on the list. -/
def shiftedGapSourceCell {signature : ModeSignature} {baseRel : CellRel signature} {oneMode : signature.graph.Mode}
    (wall : ModalityPath signature.graph oneMode oneMode) :
    (fills : List (ShiftedGapFill signature baseRel oneMode)) →
    RawTwoCellExpr signature (shiftedGapDom wall fills) (shiftedGapCod wall fills)
  | [] => RawTwoCellExpr.id (identityPath oneMode)
  | gap :: rest =>
      RawTwoCellExpr.hcomp (RawTwoCellExpr.id wall)
        (RawTwoCellExpr.hcomp gap.source (shiftedGapSourceCell wall rest))

/-- The **target layout CELL** — the all-gaps-normalized wall/gap cell: each gap's `target` in place of `source`.
Same boundary `shiftedGapDom ⇒ shiftedGapCod` (the walls and gap boundaries are unchanged; only the interior gap
cells are normalized). -/
def shiftedGapTargetCell {signature : ModeSignature} {baseRel : CellRel signature} {oneMode : signature.graph.Mode}
    (wall : ModalityPath signature.graph oneMode oneMode) :
    (fills : List (ShiftedGapFill signature baseRel oneMode)) →
    RawTwoCellExpr signature (shiftedGapDom wall fills) (shiftedGapCod wall fills)
  | [] => RawTwoCellExpr.id (identityPath oneMode)
  | gap :: rest =>
      RawTwoCellExpr.hcomp (RawTwoCellExpr.id wall)
        (RawTwoCellExpr.hcomp gap.target (shiftedGapTargetCell wall rest))

/-! ## THE WIRE-CHANGING FORWARD SPLICE -/

/-- ★★★ **THE WIRE-CHANGING (shifted) FORWARD SPLICE.**  A LIST of wire-changing wall/gap fills splices into ONE
boundary convertibility: the presented source layout `shiftedGapSourceCell wall fills` is saturated-convertible to
the normalized target layout `shiftedGapTargetCell wall fills`.  Structural on the list — `[]` is `refl` on the
empty layout; `gap :: rest` threads the head gap's `fill` (and the tail's spliced convertibility) through the
two-sided horizontal congruence `hcompCongr`, with `refl` on the inert `s`-wall.  Pure horizontal congruence
closure — the wall SHIFT is absorbed by `hcomp`'s definitional boundary, NO `castBoundary` bookkeeping survives.
Over ANY signature and base relation, hypothesis-FREE.  This upgrades r5's fixed-wire `multiGapEndoSplice` to the
WIRE-CHANGING case. -/
def multiGapShiftedSplice {signature : ModeSignature} {baseRel : CellRel signature} {oneMode : signature.graph.Mode}
    (wall : ModalityPath signature.graph oneMode oneMode) :
    (fills : List (ShiftedGapFill signature baseRel oneMode)) →
    SaturatedConvOver signature baseRel (shiftedGapSourceCell wall fills) (shiftedGapTargetCell wall fills)
  | [] => SaturatedConvOver.refl (RawTwoCellExpr.id (identityPath oneMode))
  | gap :: rest =>
      SaturatedConvOver.hcompCongr (SaturatedConvOver.refl (RawTwoCellExpr.id wall))
        (SaturatedConvOver.hcompCongr gap.fill (multiGapShiftedSplice wall rest))

/-! ## Non-vacuity — a genuinely wire-changing, two-`s`-wall word normalized end-to-end -/

/-- A **wire-changing gap fill** — the reconstructed MONAD ASSOCIATIVITY gap `t·t·t ⇒ t` (`reconAssocLeftCell` /
`reconAssocRightCell`), right-coprojected into the pushout, made convertible by the shipped base-case NF collapse
`pushoutAssocGapConv`.  A genuine `mu`-firing gap: the wire count changes `3 ⇒ 1`, so the wall to its right SHIFTS
by `2`. -/
def shiftedAssocGapFill :
    ShiftedGapFill involutionMonadPushout.toModeSignature crossPairRealPushoutRel monadPushMode :=
  ⟨_, _,
    mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) reconAssocLeftCell,
    mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) reconAssocRightCell,
    pushoutAssocGapConv⟩

/-- An **endo gap fill** — the reconstructed LEFT-UNIT gap `t ⇒ t` (`reconLeftUnitCell` / `reconIdTCell`),
right-coprojected and made convertible by `pushoutLeftUnitGapConv`.  A wire-PRESERVING gap (`1 ⇒ 1`), demonstrating
the shifted splice subsumes the endo case. -/
def shiftedLeftUnitGapFill :
    ShiftedGapFill involutionMonadPushout.toModeSignature crossPairRealPushoutRel monadPushMode :=
  ⟨_, _,
    mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) reconLeftUnitCell,
    mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) reconIdTCell,
    pushoutLeftUnitGapConv⟩

/-- ★★ **The wire-changing splice fires on a genuine two-`s`-wall word.**  `multiGapShiftedSplice` on the two-gap
layout `[assoc (t^3 ⇒ t), leftUnit (t ⇒ t)]` (walls `s` before each) produces a single pushout convertibility from
the presented layout `s·(mu-assoc)·s·(eta-unit)` to its normalized form — a genuinely WIRE-CHANGING (the first gap
shifts the second wall by `2`), TWO-`s`-wall word normalized END-TO-END.  The non-vacuity `multiGapEndoSplice`
lacked: here the gaps CHANGE the wire count. -/
def shiftedTwoGapSpliceWitness :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (shiftedGapSourceCell monadPushSPath [shiftedAssocGapFill, shiftedLeftUnitGapFill])
      (shiftedGapTargetCell monadPushSPath [shiftedAssocGapFill, shiftedLeftUnitGapFill]) :=
  multiGapShiftedSplice monadPushSPath [shiftedAssocGapFill, shiftedLeftUnitGapFill]

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the WIRE-CHANGING (shifted) forward splice SHIPS (WP-AMALG-2 r6, B2).**  `= true`:
`multiGapShiftedSplice` splices an ARBITRARY LIST of WIRE-CHANGING wall/gap fills (`ShiftedGapFill`, boundaries
PACKED so `gapDom ≠ gapCod`) into one boundary convertibility `shiftedGapSourceCell ≈ shiftedGapTargetCell`,
structural on the list via the two-sided horizontal congruence `SaturatedConvOver.hcompCongr` (built from the
shipped one-sided `hcompCongrLeft` / `hcompCongrRight`) and `refl` on the inert `s`-walls.  The wall SHIFT (B1: a
gap `t^a ⇒ t^b` moves the walls to its right by `b − a`) is ABSORBED by `hcomp`'s definitional boundary — NO
`castBoundary` bookkeeping survives, the one non-triviality the endo case dodged.  Non-vacuous on a genuinely
wire-changing, two-`s`-wall word (`shiftedTwoGapSpliceWitness`: `s·(t·t·t)·s·t`, a `mu`-associativity gap shifting
the second wall by `2` plus an endo left-unit gap, both per-gap fills the shipped right-image collapses).  This
upgrades r5's fixed-wire `multiGapEndoSplice` to the wire-changing case — the SOUNDNESS/forward direction of the
first horn.  The CONVERSE (arbitrary cell FACTORS into shifted-gap form) stays walled
(`PushoutWireChangeLedger.lean`); #2043 does NOT close.  `= true`. -/
def fxAmalg_hasShiftedGapForwardSplice : Bool := true

end FX1Poly.Polygraph.Amalgam
