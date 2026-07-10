import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalLayout

/-! # Polygraph/TwoCategory/Amalgam/PushoutVcompInterchangeSplice — THE CRUX: the vcomp case of the whole-cell
factorization induction, built FREE from iterated interchange (WP-AMALG-2 r7, B2)

`PushoutWireChangeLedger.lean` (r6) named the whole-cell factorization induction as the genuine residual and handed
its interleaved-firing-regrouping cochain to #2140 as the FIRST 2-cocycle candidate with the open question "does
the interleaved-monad-firing regrouping cochain BOUND?"  This file ANSWERS it, at the disjoint `involution +_M
monad` scope: **it BOUNDS**.  The vcomp case of the factorization induction — the crux, the pushout analogue of the
monad lane's own `wordMul_vcompGen` — is `vcompGapInterchangeSplice`, and it is built from ITERATED FREE
`TwoCellStep.interchange` with ZERO `castBoundary` bookkeeping.

## Why the cochain bounds: interchange is a coboundary (the reclassification)

The recon feared the regrouping might be a genuine H² coherence obstruction.  It is not.  The middle-four
interchange `(A ⊠ B) ⊟ (C ⊠ D) ≈ (A ⊟ C) ⊠ (B ⊟ D)` is a FREE constructor (`TwoCellStep.interchange`, cast-free —
both Godement orders share the boundary), available inside every `SaturatedConvOver` over any signature, INCLUDING
the pushout `involutionMonadPushout.toModeSignature`.  The r6 monad lane spent ~100 dense cast lines on
`wordMul_vcompGen` only because `wordFromCounts` / `composeCounts` carry `composePath`-associativity casts; the
CANONICAL LAYOUT (`PushoutCanonicalLayout.lean`) interleaves the walls so every boundary is built with matching
`composePath` nesting and NO cast survives.  So the regrouping cochain is trivialized by a free coboundary —
reclassifying the #2140 wall from "possible H² obstruction" to "authorable cast-free engineering" at the disjoint
scope.

## What ships (each zero-axiom, STRUCTURAL on the gap list, ASCII-only)

  * **`SaturatedConvOver.vcompHcompSplit`** — the free interchange packaged for the saturated conv (the generic
    pushout analogue of the monad lane's `monadVcompHcompSplitGen`): `(A ⊠ B) ⊟ (C ⊠ D) ≈ (A ⊟ C) ⊠ (B ⊟ D)`,
    one `symm` of `TwoCellStep.interchange`, over ANY signature and base relation.
  * **`vcompGapInterchangeSplice`** — THE CRUX: a vertical composite of the upper and lower cell layouts is
    saturated-convertible to the single vcomp layout (per-gap vertical composites), `vcomp (gapUpperLayout …)
    (gapLowerLayout …) ≈ gapVcompLayout …`.  Structural on the gap list; each cons fires the interchange twice
    (once to split the wall off, once per gap) and threads the tail by the IH — every step a FREE saturated conv.
  * **`hcompId_conv_idComposite` / `whiskerLeft_conv_hcompIdLeading` / `whiskerRight_conv_hcompIdTrailing`** — the
    non-crux factorization cases as free lemmas: an identity 2-cell on a composite splits as a horizontal composite
    of identities, and a whiskering equals an `id`-whisker prepend / append.  These reduce the `id` / `whiskerLeft`
    / `whiskerRight` cases of the factorization induction to the layout form.
  * **`vcompTwoGapInterchangeWitness`** — non-vacuity on the recon's hand-worked interleaved example: the two-gap,
    one-`s`-wall word with a `mu`-associativity firing (`t³ ⇒ t`) in gap 1 and a left-unit firing (`t ⇒ t`) in gap
    2, at the REAL pushout signature — the vertically-interleaved firings regrouped into one horizontal wall/gap
    cell.

## What STAYS WALLED (no flip)

This is the vcomp CASE of the factorization induction plus the non-crux reduction lemmas — NOT the top-level
induction `pushoutFactorize` (an arbitrary cell FACTORS into a `VcompGapPair` layout), which additionally needs the
`blockDecompose`↔`composePath` reconstruction bridge and the per-case assembly.  `fxAmalg_hasFullSaturatedPushoutDispatch`
(`DispatchSaturated.lean`), `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`),
`fxAmalg_factorizationCompletenessStaysWalled` (`PushoutWireChangeLedger.lean`) STAY as they are.  #2043 does NOT
close.  The advance: the crux BOUNDS, the cochain is a coboundary, the residual NARROWS to the top induction + the
decider wiring.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The free interchange, packaged for the saturated conv -/

/-- ★ **The free interchange (split direction), packaged for the generic saturated conv** — a vertical composite of
two horizontal composites is the horizontal composite of the two vertical composites: `(A ⊠ B) ⊟ (C ⊠ D) ≈ (A ⊟ C)
⊠ (B ⊟ D)`.  ONE `symm` of the cast-free `TwoCellStep.interchange` (both Godement orders share the boundary),
lifted through `SaturatedConvOver.ofConv`.  The generic pushout analogue of the monad lane's
`monadVcompHcompSplitGen` — over ANY signature and any base relation. -/
theorem SaturatedConvOver.vcompHcompSplit {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFLow oneCellFMid oneCellFHigh : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGLow oneCellGMid oneCellGHigh : ModalityPath signature.graph middleMode targetMode}
    (cellA : RawTwoCellExpr signature oneCellFLow oneCellFMid)
    (cellAUpper : RawTwoCellExpr signature oneCellFMid oneCellFHigh)
    (cellB : RawTwoCellExpr signature oneCellGLow oneCellGMid)
    (cellBUpper : RawTwoCellExpr signature oneCellGMid oneCellGHigh) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellA cellB) (RawTwoCellExpr.hcomp cellAUpper cellBUpper))
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellA cellAUpper) (RawTwoCellExpr.vcomp cellB cellBUpper)) :=
  SaturatedConvOver.symm
    (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.interchange cellA cellAUpper cellB cellBUpper)))

/-! ## THE CRUX — the vcomp case of the factorization induction -/

/-- ★★★ **THE CRUX SPLICE — the vcomp case of the whole-cell factorization induction.**  A vertical composite of
the UPPER cell layout and the LOWER cell layout is saturated-convertible to the single VCOMP cell layout (each gap
the per-gap vertical composite `vcomp upper lower`): `vcomp (gapUpperLayout finalWall pairs) (gapLowerLayout
finalWall pairs) ≈ gapVcompLayout finalWall pairs`.

Structural recursion on the gap list.  `[]` — both layouts are `id finalWall`; `vcomp (id finalWall) (id finalWall)
≈ id finalWall` by `vcompIdLeft`.  `pair :: rest` — the outer `vcompHcompSplit` peels the leading wall off both
layouts, turning `vcomp (wall ⊠ restUp) (wall ⊠ restLow)` into `(wall ⊟ wall) ⊠ (restUp ⊟ restLow)`; the left
factor collapses `vcomp (id wall) (id wall) ≈ id wall` (free `vcompIdLeft`); the right factor fires the interchange
AGAIN to split the head gap off (`vcompHcompSplit pair.upper pair.lower …`), then threads the tail by the IH
through `hcompCongrRight`.  Every step a FREE saturated conv — no `castBoundary`, because the canonical layout
interleaves the walls so every boundary lines up definitionally.  This is the pushout analogue of the monad lane's
`wordMul_vcompGen`, cast-free.  Over ANY signature and base relation — the interleaved-firing regrouping cochain
BOUNDS (the #2140 answer). -/
theorem vcompGapInterchangeSplice {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.vcomp (gapUpperLayout finalWall pairs) (gapLowerLayout finalWall pairs))
      (gapVcompLayout finalWall pairs)
  | [] =>
      SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id finalWall)))
  | pair :: rest =>
      SaturatedConvOver.trans
        (SaturatedConvOver.vcompHcompSplit (RawTwoCellExpr.id pair.wall) (RawTwoCellExpr.id pair.wall)
          (RawTwoCellExpr.hcomp pair.upper (gapUpperLayout finalWall rest))
          (RawTwoCellExpr.hcomp pair.lower (gapLowerLayout finalWall rest)))
        (SaturatedConvOver.hcompCongr
          (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id pair.wall))))
          (SaturatedConvOver.trans
            (SaturatedConvOver.vcompHcompSplit pair.upper pair.lower
              (gapUpperLayout finalWall rest) (gapLowerLayout finalWall rest))
            (SaturatedConvOver.hcompCongrRight (RawTwoCellExpr.vcomp pair.upper pair.lower)
              (vcompGapInterchangeSplice finalWall rest))))

/-! ## The non-crux factorization cases as free reduction lemmas -/

/-- The identity 2-cell on a composite splits as a horizontal composite of identities: `hcomp (id a) (id b) ≈
id (composePath a b)`.  `hcomp (id a) (id b) = vcomp (whiskerRight b (id a)) (whiskerLeft a (id b))`, both
whiskerings of an identity reduce (`whiskerRightId` / `whiskerLeftId`) to `id (composePath a b)`, then
`vcompIdLeft`.  The `id` case of the factorization induction. -/
theorem hcompId_conv_idComposite {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (pathLeft : ModalityPath signature.graph sourceMode middleMode)
    (pathRight : ModalityPath signature.graph middleMode targetMode) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.id pathLeft) (RawTwoCellExpr.id pathRight))
      (RawTwoCellExpr.id (composePath pathLeft pathRight)) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrLeft (RawTwoCellExpr.whiskerLeft pathLeft (RawTwoCellExpr.id pathRight))
      (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerRightId pathLeft pathRight))))
    (SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrRight (RawTwoCellExpr.id (composePath pathLeft pathRight))
        (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId pathLeft pathRight))))
      (SaturatedConvOver.ofConv
        (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id (composePath pathLeft pathRight))))))

/-- A left whiskering equals an `id`-whisker PREPEND: `whiskerLeft oneCell body ≈ hcomp (id oneCell) body`.
`hcomp (id oneCell) body = vcomp (whiskerRight body.dom (id oneCell)) (whiskerLeft oneCell body)`; the whiskered
identity reduces (`whiskerRightId`) to `id (composePath oneCell body.dom)`, then `vcompIdLeft` drops it.  The
`whiskerLeft` case of the factorization induction (prepend `oneCell`'s blocks to `body`'s layout). -/
theorem whiskerLeft_conv_hcompIdLeading {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {bodyDom bodyCod : ModalityPath signature.graph middleMode targetMode}
    (body : RawTwoCellExpr signature bodyDom bodyCod) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerLeft oneCell body)
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.id oneCell) body) :=
  SaturatedConvOver.symm
    (SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrLeft (RawTwoCellExpr.whiskerLeft oneCell body)
        (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerRightId oneCell bodyDom))))
      (SaturatedConvOver.ofConv
        (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (RawTwoCellExpr.whiskerLeft oneCell body)))))

/-- A right whiskering equals an `id`-whisker APPEND: `whiskerRight oneCell body ≈ hcomp body (id oneCell)`.
`hcomp body (id oneCell) = vcomp (whiskerRight oneCell body) (whiskerLeft body.cod (id oneCell))`; the whiskered
identity reduces (`whiskerLeftId`) to `id (composePath body.cod oneCell)`, then `vcompIdRight` drops it.  The
`whiskerRight` case of the factorization induction (append `oneCell`'s blocks to `body`'s layout). -/
theorem whiskerRight_conv_hcompIdTrailing {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {bodyDom bodyCod : ModalityPath signature.graph sourceMode middleMode}
    (body : RawTwoCellExpr signature bodyDom bodyCod) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerRight oneCell body)
      (RawTwoCellExpr.hcomp body (RawTwoCellExpr.id oneCell)) :=
  SaturatedConvOver.symm
    (SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrRight (RawTwoCellExpr.whiskerRight oneCell body)
        (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId bodyCod oneCell))))
      (SaturatedConvOver.ofConv
        (TwoCellConv.ofStep (TwoCellStep.vcompIdRight (RawTwoCellExpr.whiskerRight oneCell body)))))

/-! ## Non-vacuity — the recon's hand-worked interleaved firing, at the real pushout signature -/

/-- The right-coprojection of a reconstructed monad cell into the `involution +_M monad` pushout — the shorthand
the interleaved witness uses to name its gap payloads. -/
abbrev pushoutRightCell {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath) :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (mapPath (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes).toComputadMorphism
        sourcePath)
      (mapPath (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes).toComputadMorphism
        targetPath) :=
  mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cell

/-- The empty leading wall at the pushout mode — an `id` wall for a gap-first word (the result-type annotation
pins the graph). -/
def pushoutTrivialWall : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode :=
  ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode

/-- Gap 1 of the interleaved witness — the `mu`-associativity firing `t³ ⇒ t` on top, IDLE (`id` on `t`) on the
bottom.  The right-coprojected `reconAssocLeftCell` as `upper`, an identity as `lower`; the leading wall is empty
(the word starts with a gap). -/
def interleavedAssocGapPair : VcompGapPair involutionMonadPushout.toModeSignature monadPushMode where
  wall := pushoutTrivialWall
  gapDom := _
  gapMid := _
  gapCod := _
  upper := pushoutRightCell reconAssocLeftCell
  lower := RawTwoCellExpr.id _

/-- Gap 2 of the interleaved witness — IDLE (`id` on `t`) on top, the left-unit firing `t ⇒ t` on the bottom.  An
identity as `upper`, the right-coprojected `reconLeftUnitCell` as `lower`; the leading wall is the single `s`-wall
`monadPushSPath`. -/
def interleavedLeftUnitGapPair : VcompGapPair involutionMonadPushout.toModeSignature monadPushMode where
  wall := monadPushSPath
  gapDom := _
  gapMid := _
  gapCod := _
  upper := RawTwoCellExpr.id _
  lower := pushoutRightCell reconLeftUnitCell

/-- ★★ **The crux fires on the recon's hand-worked interleaved firing.**  `vcompGapInterchangeSplice` on the
two-gap, one-`s`-wall layout `[assoc-in-gap-1, leftUnit-in-gap-2]` (over the REAL pushout signature) produces a
single pushout saturated conv from the VERTICAL composite of the two stacked layouts — `(α ⊠ s ⊠ id_t) ⊟ (id_t ⊠ s
⊠ β)` — to the single HORIZONTAL wall/gap cell `(α ⊟ id_t) ⊠ s ⊠ (id_t ⊟ β)`.  The two vertically-interleaved
firings (`mu`-associativity `t³ ⇒ t` in gap 1, left-unit `t ⇒ t` in gap 2, each idle in the other gap) are
regrouped into one horizontal wall/gap cell — exactly the r6-ledger interleaved-firing regrouping, now MACHINE
witnessed, cast-free, at the disjoint scope.  The per-gap collapse `α ⊟ id_t ≈ α` / `id_t ⊟ β ≈ β` is the shipped
`pushoutRightImageTwoSidedDecision` reseat (the second half). -/
def vcompTwoGapInterchangeWitness :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (RawTwoCellExpr.vcomp
        (gapUpperLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair])
        (gapLowerLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair]))
      (gapVcompLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair]) :=
  vcompGapInterchangeSplice pushoutTrivialWall
    [interleavedAssocGapPair, interleavedLeftUnitGapPair]

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — THE CRUX vcomp-case splice SHIPS (WP-AMALG-2 r7, B2).**  `= true`:
`vcompGapInterchangeSplice` discharges the vcomp case of the whole-cell factorization induction — `vcomp
(gapUpperLayout …) (gapLowerLayout …) ≈ gapVcompLayout …` — structurally on the gap list, built from iterated FREE
`TwoCellStep.interchange` (packaged as `SaturatedConvOver.vcompHcompSplit`) with ZERO `castBoundary` bookkeeping,
over ANY signature.  The pushout analogue of the monad lane's `wordMul_vcompGen`, cast-free (the canonical layout
interleaves the walls so boundaries line up definitionally).  The non-crux cases ship as free reduction lemmas
(`hcompId_conv_idComposite`, `whiskerLeft_conv_hcompIdLeading`, `whiskerRight_conv_hcompIdTrailing`).  Non-vacuous
on the recon's hand-worked interleaved firing at the REAL pushout signature (`vcompTwoGapInterchangeWitness`: a
`mu`-associativity `t³ ⇒ t` in gap 1 and a left-unit `t ⇒ t` in gap 2, one `s`-wall between, regrouped into one
horizontal wall/gap cell).  `= true`. -/
def fxAmalg_hasVcompGapInterchangeSplice : Bool := true

/-- ★★ **Honesty marker — the #2140 interleaved-firing regrouping cochain BOUNDS (the r6 handoff answered).**
`= true`: the r6 ledger (`PushoutWireChangeLedger.fxAmalg_h2ExtCocycleHandoff`) handed #2140 the open question "does
the interleaved-monad-firing regrouping cochain BOUND?"  At the disjoint `involution +_M monad` scope the answer is
YES — `vcompGapInterchangeSplice` trivializes the regrouping by a FREE coboundary (`TwoCellStep.interchange` is a
cast-free constructor inside every saturated conv), so the cochain is a coboundary, NOT a genuine H² class.  This
RECLASSIFIES the r6 wall from "possible H² coherence obstruction" to "authorable cast-free engineering" — a real
narrowing over the r6 hedge.  (Provenance: the monad lane's `wordMul_vcompGen` needed ~100 cast lines only because
`wordFromCounts` carries `composePath`-associativity casts; the interleaved canonical layout carries none.)  This
is a RECLASSIFICATION marker, not a claim that the top induction is discharged.  `= true`. -/
def fxAmalg_vcompRegroupCochainBounds : Bool := true

/-- **Honesty marker — the TOP-LEVEL factorization induction STAYS WALLED (no flip).**  `= true` (the wall is
honestly held).  This file ships the vcomp CASE (`vcompGapInterchangeSplice`) + the non-crux reduction lemmas, but
NOT the top-level `pushoutFactorize` (an arbitrary pushout cell FACTORS into a `VcompGapPair` layout with a
convertibility to it).  That top induction additionally needs: (a) the `blockDecompose`↔`composePath`
reconstruction bridge to READ a canonical `VcompGapPair` list off an arbitrary cell's boundary; (b) the per-case
assembly (the `gen` case = one pure-`t` gap, the `id` / `whisker` cases via the reduction lemmas here, the `vcomp`
case via the crux) producing a single layout keyed to the CANONICAL block decomposition; (c) the decider wiring
(`pushoutFullTwoSidedDecision` from the factorization + `pushoutRightImageTwoSidedDecision` + `multiGapShiftedSplice`
+ `arityFoldRealPushoutCongruence`).  `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS
`false`, `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`,
`fxAmalg_factorizationCompletenessStaysWalled` (`PushoutWireChangeLedger.lean`) STAYS `true`.  #2043 does NOT close.
Named node: the top-level `pushoutFactorize` induction assembly + decider wiring.  No fabricated flip.  `= true`. -/
def fxAmalg_topFactorizationInductionStaysWalled : Bool := true

end FX1Poly.Polygraph.Amalgam
