import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutLayoutFactorization
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallCountInvariance
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellInvert

/-! # Polygraph/TwoCategory/Amalgam/PushoutFactorizeGenCase — the `gen` case of the top factorization: an atomic
2-generator occupies a SINGLE firing slot with wall-free boundaries (WP-AMALG-2 r15, Brick B1)

`PushoutLayoutFactorization.lean` (r8) shipped the MOTIVE and the `id` case (`pushoutFactorizeId`, the empty layout).
This file ships the `gen` case — the second base case of the top induction `pushoutFactorize`.

## The construction — one gap, no walls

A single 2-cell `cell : A ⇒ B` factors through the SINGLE-GAP layout: `finalWall = id`, one `VcompGapPair` with an
empty leading wall (`wall = id`), gap domain `A`, gap middle/codomain `B`, the whole cell as `upper`, and `id B` as
`lower`.  The layout boundaries are `composePath A id` (domain) and `composePath B id` (codomain), which equal `A` /
`B` by `composePath_identityPath_right` (NOT `rfl` — the trailing `id`-wall introduces a right-unit cast), and the
convertibility reduces the layout's leading / trailing `id`-whisker gadgets through the `TwoCellConvFull` whisker
UNITORS (`whiskerLeftUnit` / `whiskerRightUnit`) and drops the `id B` lower payload by `vcompIdRight`.

This is the GENERIC single-gap factorization — it holds for ANY cell over ANY signature.  For a bare 2-generator it
is the CANONICAL answer: a `gen` is one atomic firing, occupying exactly one gap.  The truth-probes below certify
(via `pushoutTwoGen_words_wallFree` + `wallLetterCount_dom_eq_cod`) that the pushout's two reconstructed generators
`eta` (`id ⇒ t`) and `mu` (`t·t ⇒ t`) have WALL-FREE boundaries at BOTH ends — so their single slot carries no wall,
confirming `noGeneratorStraddlesWall`: no generator straddles a wall, so the single-slot placement is sound however
many `s`-walls flank the gen in its surrounding whisker context.

## What ships (each zero-axiom, ASCII-only, STRUCTURAL / term-level)

  * **`singleGapPair`** — the one wall/gap block carrying a whole cell (`wall = id`, `upper = cell`, `lower = id`).
  * **`singleGapLayoutConv`** — the convertibility: the boundary-cast cell is saturated-convertible to the single-gap
    layout's `gapVcompLayout`, over ANY signature / base relation (the whisker-unitor + `vcompIdRight` reduction).
  * **`pushoutFactorizeSingleGap`** — the generic single-gap `PushoutLayoutFactorization` of an arbitrary cell.
  * **`pushoutFactorizeGen`** — the `gen` case: a bare 2-generator's single-gap factorization.
  * **`pushoutEtaFactorization` / `pushoutMultFactorization`** — the two concrete pushout generators factored.
  * **`pushoutEtaSlotWallFree` / `pushoutMultSlotWallFree`** — the wall-free-slot truth-probes (the gen's gap
    boundaries carry ZERO walls at both ends).

## What STAYS WALLED (no flip)

This ships the `gen` case, NOT the total `pushoutFactorize`: the general `whisker` frame-merge and the `vcomp`
firing-block alignment remain (the atomic-firing residual).  `fxAmalg_topFactorizationInductionStaysWalled`
(`PushoutVcompInterchangeSplice.lean`) STAYS `true`; the masters STAY at their walled values; #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The single-gap block -/

/-- The **single-gap block** carrying a whole cell — one `VcompGapPair` with an EMPTY leading wall (`wall = id`),
gap domain the cell's domain, gap middle / codomain the cell's codomain, the whole `cell` as the `upper` payload,
and `id` (the codomain) as the `lower` payload.  This is the canonical slot of a bare firing: no wall, one gap, the
atomic cell inside. -/
def singleGapPair {signature : ModeSignature} {oneMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : VcompGapPair signature oneMode where
  wall := ModalityPath.nil oneMode
  gapDom := sourcePath
  gapMid := targetPath
  gapCod := targetPath
  upper := cell
  lower := RawTwoCellExpr.id targetPath

/-! ## The single-gap convertibility -/

/-- ★★ **The single-gap layout convertibility.**  The boundary-cast cell (`castBoundary` through the right-unit
equalities `composePath A id = A` / `composePath B id = B`) is saturated-convertible to the single-gap layout's
`gapVcompLayout id [singleGapPair cell] = (id_id) ⊠ ((cell ⊟ id_B) ⊠ id_id)`.  The reduction, over ANY signature and
base relation:

  * the OUTER leading `id`-whisker gadget `hcomp (id id) inner` reduces to `inner` — `whiskerLeft_conv_hcompIdLeading`
    turns it into `whiskerLeft id inner`, then the `TwoCellConvFull` unitor `whiskerLeftUnit` strips the unit
    whisker;
  * the INNER trailing `id`-whisker gadget `hcomp (cell ⊟ id_B) (id id)` reduces to `whiskerRight id (cell ⊟ id_B)`
    (`whiskerRight_conv_hcompIdTrailing`), which the unitor `whiskerRightUnit` sends to the boundary-cast of
    `cell ⊟ id_B`;
  * the `id_B` lower payload drops by `vcompIdRight`, transported under the cast by `castBoundaryCongr`. -/
theorem singleGapLayoutConv {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.castBoundary (composePath_identityPath_right sourcePath).symm
        (composePath_identityPath_right targetPath).symm cell)
      (gapVcompLayout (ModalityPath.nil oneMode) [singleGapPair cell]) :=
  SaturatedConvOver.symm
    (SaturatedConvOver.trans
      (SaturatedConvOver.trans
        (SaturatedConvOver.symm
          (whiskerLeft_conv_hcompIdLeading (ModalityPath.nil oneMode)
            (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cell (RawTwoCellExpr.id targetPath))
              (RawTwoCellExpr.id (ModalityPath.nil oneMode)))))
        (SaturatedConvOver.ofFull
          (TwoCellConvFull.whiskerLeftUnit
            (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cell (RawTwoCellExpr.id targetPath))
              (RawTwoCellExpr.id (ModalityPath.nil oneMode))))))
      (SaturatedConvOver.trans
        (SaturatedConvOver.symm
          (whiskerRight_conv_hcompIdTrailing (ModalityPath.nil oneMode)
            (RawTwoCellExpr.vcomp cell (RawTwoCellExpr.id targetPath))))
        (SaturatedConvOver.trans
          (SaturatedConvOver.ofFull
            (TwoCellConvFull.whiskerRightUnit (RawTwoCellExpr.vcomp cell (RawTwoCellExpr.id targetPath))))
          (SaturatedConvOver.castBoundaryCongr
            (composePath_identityPath_right sourcePath).symm
            (composePath_identityPath_right targetPath).symm
            (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight cell)))))))

/-! ## The generic single-gap factorization + the `gen` case -/

/-- ★★ **The generic single-gap factorization.**  An ARBITRARY cell `cell : A ⇒ B` factors as the single-gap layout
(`finalWall = id`, one `singleGapPair cell`): boundary equalities the right-unit `composePath_identityPath_right`,
convertibility `singleGapLayoutConv`.  Over ANY signature / base relation.  This is the trivial one-firing-slot
factorization; the `gen` case specializes it, where the single gap is the CANONICAL firing region (a generator is
atomic). -/
def pushoutFactorizeSingleGap {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    PushoutLayoutFactorization baseRel cell where
  finalWall := ModalityPath.nil oneMode
  pairs := [singleGapPair cell]
  domEq := (composePath_identityPath_right sourcePath).symm
  codEq := (composePath_identityPath_right targetPath).symm
  conv := singleGapLayoutConv cell

/-- ★★★ **THE `gen` CASE of the top factorization.**  A bare 2-generator `gen g : A ⇒ B` factors as its single
canonical firing slot (`pushoutFactorizeSingleGap` on `RawTwoCellExpr.gen g`).  The second base case of the top
induction `pushoutFactorize` (the first being `pushoutFactorizeId`).  Generic over signature / base relation. -/
def pushoutFactorizeGen {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    (g : signature.twoCell sourcePath targetPath) :
    PushoutLayoutFactorization baseRel (RawTwoCellExpr.gen g) :=
  pushoutFactorizeSingleGap baseRel (RawTwoCellExpr.gen g)

/-! ## The concrete pushout generators factored -/

/-- ★★ **The pushout monad unit `eta` (`id ⇒ t`) factored.**  Its single canonical slot: one gap `id ⇒ t` carrying
`eta`, no walls.  A concrete `gen`-case factorization at the REAL pushout signature. -/
def pushoutEtaFactorization :
    PushoutLayoutFactorization crossPairRealPushoutRel pushoutEta :=
  pushoutFactorizeGen crossPairRealPushoutRel pushoutMonadUnit

/-- ★★ **The pushout monad multiplication `mu` (`t·t ⇒ t`) factored.**  Its single canonical slot: one gap
`t·t ⇒ t` carrying `mu`, no walls.  The `mu`-firing whose atomicity (`mu` spans two `t` letters) is the crux of the
`vcomp` alignment residual — here at the `gen` granularity it sits in ONE slot, undivided. -/
def pushoutMultFactorization :
    PushoutLayoutFactorization crossPairRealPushoutRel (RawTwoCellExpr.gen pushoutMonadMult) :=
  pushoutFactorizeGen crossPairRealPushoutRel pushoutMonadMult

/-! ## Truth-probes — the gen slot is wall-free at BOTH ends (`noGeneratorStraddlesWall`, concrete) -/

/-- ★★ **TRUTH-PROBE (unit slot wall-free).**  The `eta` gap's boundaries `id ⇒ t` each carry ZERO walls
(`pushoutPathWallCount` of both `id` and `t` is `0`).  So the single slot placing `eta` has an empty wall on the
left and a wall-free gap — the canonical firing region, no `s` in the fired window. -/
theorem pushoutEtaSlotWallFree :
    pushoutPathWallCount
        (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) = 0
      ∧ pushoutPathWallCount monadPushTPath = 0 :=
  ⟨rfl, rfl⟩

/-- ★★ **TRUTH-PROBE (mult slot wall-free).**  The `mu` gap's boundaries `t·t ⇒ t` each carry ZERO walls — even the
two-letter domain `t·t` is pure component-2, no `s`.  This is the concrete `noGeneratorStraddlesWall`: the `mu`
firing, however wall-heavy its surrounding whisker frame, occupies a wall-free slot; its domain never contains an
`s` for it to straddle. -/
theorem pushoutMultSlotWallFree :
    pushoutPathWallCount (composePath monadPushTPath monadPushTPath) = 0
      ∧ pushoutPathWallCount monadPushTPath = 0 :=
  ⟨rfl, rfl⟩

/-- ★ **The gen-boundary wall-count is dom-to-cod invariant (the general statement, instantiated).**  For the
concrete `mu` generator, `wallLetterCount_dom_eq_cod` gives `pushoutPathWallCount (t·t) = pushoutPathWallCount t`
directly — a machine confirmation that the single slot's two boundaries carry the same (zero) wall count. -/
theorem pushoutMultBoundaryWallCountEq :
    pushoutPathWallCount (composePath monadPushTPath monadPushTPath) = pushoutPathWallCount monadPushTPath :=
  wallLetterCount_dom_eq_cod (RawTwoCellExpr.gen pushoutMonadMult)

/-! ## Observability -/

-- The `eta` gap slot: domain word `[]` (wall count 0), codomain word `[t]` (wall count 0).
#eval (pushoutPathWallCount (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode),
  pushoutPathWallCount monadPushTPath)
-- The `mu` gap slot: domain word `[t, t]` (wall count 0), codomain word `[t]` (wall count 0).
#eval (pushoutPathWallCount (composePath monadPushTPath monadPushTPath), pushoutPathWallCount monadPushTPath)

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the `gen` case of the top factorization SHIPS; the total induction STAYS WALLED
(WP-AMALG-2 r15, B1).**  `= true`.  A bare 2-generator factors as its single canonical firing slot
(`pushoutFactorizeGen`, an instance of the generic `pushoutFactorizeSingleGap`): one gap carrying the gen, no walls,
boundary casts the right-unit `composePath_identityPath_right`, convertibility `singleGapLayoutConv` (whisker unitors
`whiskerLeftUnit` / `whiskerRightUnit` strip the leading / trailing `id`-whisker gadgets, `vcompIdRight` drops the
`id` lower payload — over ANY signature).  Non-vacuous at the REAL pushout signature: `eta` (`id ⇒ t`) and `mu`
(`t·t ⇒ t`) factor concretely (`pushoutEtaFactorization` / `pushoutMultFactorization`), and their slots are wall-free
at BOTH ends (`pushoutEtaSlotWallFree` / `pushoutMultSlotWallFree`, and `pushoutMultBoundaryWallCountEq` via
`wallLetterCount_dom_eq_cod`) — the concrete `noGeneratorStraddlesWall`: no generator's boundary contains an `s`, so
the single-slot placement is sound however many walls flank the gen.

This ships the SECOND base case (`id` was the first).  It does NOT ship the total `pushoutFactorize`: the general
`whisker` frame-merge (`mergeFrameIntoHead/Tail`) and the `vcomp` firing-block alignment (the atomic-firing residual)
remain.  `fxAmalg_topFactorizationInductionStaysWalled` (`PushoutVcompInterchangeSplice.lean`) STAYS `true`;
`fxAmalg_hasFullSaturatedPushoutDispatch` / `fxAmalg_hasGeneralPushoutDispatch` STAY `false`.  #2043 does NOT close.
No fabricated flip.  `= true`. -/
def fxAmalg_hasGenCaseFactorization : Bool := true

end FX1Poly.Polygraph.Amalgam
