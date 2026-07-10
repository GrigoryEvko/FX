import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompInterchangeSplice
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallBlockScaffold

/-! # Polygraph/TwoCategory/Amalgam/PushoutLayoutFactorization — the factorization MOTIVE + the easy cases, and the
positive counterpoint to the wall-block refutation (WP-AMALG-2 r8, B1)

`PushoutWallBlockScaffold.lean` (r8, this round) refuted the recon's wall-block-keyed ALIGNMENT strategy for the
top-level `pushoutFactorize`.  This file ships the factorization MOTIVE it was aiming at, the two clean cases
(`id`, and the concrete wall-splitting witness), and — the honest counterpoint — the demonstration that the
factorization GOAL survives the refutation: the very cell that breaks wall-block conservation STILL factors as a
well-formed `eta`-gap layout.

## The motive

`PushoutLayoutFactorization baseRel cell` packages a `VcompGapPair` layout (`finalWall` + `pairs`, from
`PushoutCanonicalLayout.lean`) whose domain / codomain 1-cell layouts match the cell's boundaries (`domEq` /
`codEq`), together with a saturated convertibility from the (boundary-cast) cell to the layout's `gapVcompLayout`.
This is the per-cell output the top induction `pushoutFactorize` would produce, EXISTENTIAL over the layout.

## What ships (each zero-axiom, ASCII-only)

  * **`PushoutLayoutFactorization`** — the motive (data layout + `SaturatedConvOver` convertibility), generic over
    signature / base relation / single mode.
  * **`pushoutFactorizeId`** — the `id` case: the empty layout, `rfl` boundary casts, `refl` convertibility.
  * **`unitSplitsWallPair`** / **`unitSplitsWallFactorization`** — the POSITIVE counterpoint: the wall-splitting
    cell `unitSplitsWallCell` (`s·s ==> s·t·s`, whose wall-block lists DIFFER dom-to-cod) nonetheless factors as a
    single `eta`-gap between an `s`-wall and a trailing `s`-wall (`finalWall = s`, one gap `nil ==> t` carrying
    `eta`).  Built from the shipped free reduction lemmas (`whiskerLeft_conv_hcompIdLeading`,
    `whiskerRight_conv_hcompIdTrailing`, `hcompCongr*`, `vcompIdRight`), with `rfl` boundary casts.

## What STAYS WALLED (no flip)

This ships the MOTIVE and the two easy cases, NOT the total `pushoutFactorize` (the general `gen` / `whisker` /
`vcomp` assembly).  The general `vcomp` case is precisely where the recon's zip is BLOCKED
(`PushoutWallBlockScaffold.lean`: the wall-block list is not a dom-to-cod invariant, so the two recursive layouts
cannot be aligned on a shared wall scaffold).  `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`)
STAYS `false`; #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The factorization motive -/

/-- ★ **The layout factorization of a pushout 2-cell** — a `VcompGapPair` layout (`finalWall` + `pairs`) whose
domain / codomain 1-cell layouts equal the cell's boundaries (`domEq` / `codEq`), together with a saturated
convertibility from the boundary-cast cell to the layout's `gapVcompLayout` (`conv`).  This is the per-cell output
of the top-level factorization induction: an arbitrary cell is convertible to a horizontal wall/gap layout.
Generic over signature / base relation / single mode (the involution+monad pushout is `modeCount = 1`, so a single
endo-mode suffices). -/
structure PushoutLayoutFactorization {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : Type where
  /-- The trailing wall word of the layout. -/
  finalWall : ModalityPath signature.graph oneMode oneMode
  /-- The wall/gap blocks of the layout. -/
  pairs : List (VcompGapPair signature oneMode)
  /-- The cell's domain equals the layout's domain 1-cell. -/
  domEq : sourcePath = gapDomLayout finalWall pairs
  /-- The cell's codomain equals the layout's codomain 1-cell. -/
  codEq : targetPath = gapCodLayout finalWall pairs
  /-- The boundary-cast cell is saturated-convertible to the layout's vcomp cell. -/
  conv : SaturatedConvOver signature baseRel
    (RawTwoCellExpr.castBoundary domEq codEq cell) (gapVcompLayout finalWall pairs)

/-! ## The `id` case -/

/-- ★ **The `id` case of the factorization.**  An identity 2-cell `id path` factors as the EMPTY layout
(`finalWall = path`, no gaps): `gapDomLayout path [] = gapCodLayout path [] = path` (`rfl` casts) and
`gapVcompLayout path [] = id path`, so the convertibility is `refl`.  The base case of the top induction. -/
def pushoutFactorizeId {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    (path : ModalityPath signature.graph oneMode oneMode) :
    PushoutLayoutFactorization baseRel (RawTwoCellExpr.id path) where
  finalWall := path
  pairs := []
  domEq := rfl
  codEq := rfl
  conv := SaturatedConvOver.refl (RawTwoCellExpr.id path)

/-! ## The positive counterpoint — the wall-splitting cell DOES factor -/

/-- The single `eta`-gap block of the wall-splitting witness's factorization: a leading `s`-wall, a gap `nil ==> t`
whose `upper` is `eta` (`nil ==> t`) and whose `lower` is `id_t`.  With a trailing wall `finalWall = s`, its layout
boundaries are `s·s` (domain, the empty gap collapses the two walls) and `s·t·s` (codomain, the `t` separates
them). -/
def unitSplitsWallPair : VcompGapPair involutionMonadPushout.toModeSignature monadPushMode where
  wall := monadPushSPath
  gapDom := ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode
  gapMid := monadPushTPath
  gapCod := monadPushTPath
  upper := pushoutEta
  lower := RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushTPath

/-- ★★★ **THE POSITIVE COUNTERPOINT — the wall-splitting cell factors as an `eta`-gap layout.**  `unitSplitsWallCell`
(`whiskerLeft s (whiskerRight s eta) : s·s ==> s·t·s`), whose domain and codomain wall-block lists DIFFER
(`PushoutWallBlockScaffold.lean`), NONETHELESS has a well-formed `PushoutLayoutFactorization`: the single `eta`-gap
`unitSplitsWallPair` between a leading `s`-wall and a trailing `s`-wall.  Both boundary casts are `rfl` (the layout
boundaries `composePath s (composePath nil s)` / `composePath s (composePath t s)` are the cell's boundaries on the
nose), and the convertibility is the free chain `whiskerLeft s (whiskerRight s eta) ~ hcomp (id s) (whiskerRight s
eta) ~ hcomp (id s) (hcomp (vcomp eta id_t) (id s))` = `gapVcompLayout s [unitSplitsWallPair]`, using the shipped
reduction lemmas.  This shows the factorization GOAL survives the wall-block refutation: what the refutation blocks
is the wall-block-keyed ALIGNMENT strategy for the general `vcomp` case, NOT the existence of factorizations. -/
def unitSplitsWallFactorization :
    PushoutLayoutFactorization crossPairRealPushoutRel unitSplitsWallCell where
  finalWall := monadPushSPath
  pairs := [unitSplitsWallPair]
  domEq := rfl
  codEq := rfl
  conv := by
    refine SaturatedConvOver.trans
      (whiskerLeft_conv_hcompIdLeading monadPushSPath
        (RawTwoCellExpr.whiskerRight monadPushSPath pushoutEta)) ?_
    refine SaturatedConvOver.hcompCongrRight
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath) ?_
    refine SaturatedConvOver.trans
      (whiskerRight_conv_hcompIdTrailing monadPushSPath pushoutEta) ?_
    exact SaturatedConvOver.hcompCongrLeft
      (SaturatedConvOver.symm
        (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight pushoutEta))))
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the factorization MOTIVE + the easy cases SHIP; the general assembly stays walled
(WP-AMALG-2 r8, B1).**  `= true`: `PushoutLayoutFactorization` (the layout + convertibility motive), the `id` case
(`pushoutFactorizeId`, empty layout / `refl`), and the POSITIVE counterpoint (`unitSplitsWallFactorization`: the
wall-splitting `unitSplitsWallCell` factors as an `eta`-gap between two `s`-walls, `rfl` casts, free reduction
chain) ship.  The counterpoint is the honest complement to `PushoutWallBlockScaffold.lean`'s refutation: the
factorization GOAL is NOT refuted — a well-formed factorization exists even where the wall-block list is not
dom/cod-invariant — but the recon's wall-block-keyed ALIGNMENT of the two recursive layouts in the general `vcomp`
case IS blocked (the zip has no shared wall scaffold to key to).  So the top-level `pushoutFactorize` is NOT total
this round; `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`; #2043 does NOT
close.  No fabricated flip.  `= true`. -/
def fxAmalg_hasLayoutFactorizationMotive : Bool := true

end FX1Poly.Polygraph.Amalgam
