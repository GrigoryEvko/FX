import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeCanonical

/-! # Polygraph/TwoCategory/Amalgam/PushoutIdentityLayoutCollapse — the multi-block identity-layout COLLAPSE conv, and
the general `id`-arm canonical factorization it unlocks (WP-AMALG-2 r20, Brick B2)

r19 (`PushoutFactorizeCanonical.lean`) named the `id`-arm residual `fxAmalg_idCanonicalCollapseStaysGated`: the
multi-block identity-layout COLLAPSE conv `gapVcompLayout nil (firingBlockLayout path) ≈ castBoundary (round-trips)
(id path)` — threading the per-block `vcompIdLeft` + `hcompId_conv_idComposite` collapse through the `gapDomLayout =
gapCodLayout` boundary cast.  This file AUTHORS that collapse (the r20 mechanical arm (a) of the recon — all pieces
were shipped) and assembles the general `id`-arm `CanonicalFactorization` on top of it.

## The collapse (decoupled from the producer `bif`)

The obstacle is that `gapVcompLayout finalWall pairs : gapDomLayout … ⇒ gapCodLayout …`, and for an ABSTRACT
producer output the two boundary layouts are only PROPOSITIONALLY equal (`firingBlockLayoutAux_gapDomEqCod`), so the
collapse target `id (gapDomLayout …)` must ride a boundary cast.  Casing on the producer's `bif` inside a goal that
carries that dependent cast fails (`generalize` breaks the cast proof).  The fix DECOUPLES:

  * **`AllIdBlocks`** — a predicate isolating block lists whose every element is an `idBlockPair`.
  * **`gapVcompLayoutIdBlocksCollapse`** — the collapse over an `AllIdBlocks` list, structural on the WITNESS (no
    `bif`): `[]` is `refl`; each cons fires `idBlockPairConsVcompCollapse`, which threads the tail collapse through
    two `composePath` cast pushes (`hcomp_castBoundaryRight`) and two `hcompId_conv_idComposite` folds.
  * **`firingBlockLayoutAux_allIdBlocks`** — the producer emits an `AllIdBlocks` list, a Prop-valued path induction
    (no dependent cast, so the `bif` splits cleanly).
  * **`firingBlockLayoutIdCollapse`** — the producer-form collapse, `gapVcompLayoutIdBlocksCollapse` fed the
    producer witness; the cast proof matches `firingBlockLayoutAux_gapDomEqCod` by proof irrelevance.

## The `id`-arm canonical factorization

`pushoutFactorizeIdCanonical path` inhabits `PushoutLayoutFactorization crossPairRealPushoutRel (id path)` with
`pairs = firingBlockLayout path`, the B2 round-trips as boundary casts, and `firingBlockLayoutIdCollapse` (reassociated
by `castBoundaryIdReassoc`) as the convertibility.  `idCanonicalFactorization path` lifts it to the
`CanonicalFactorization` subtype via `firingBlockLayout_slotCount` — the general `id` arm, superseding the nil-only
`pushoutFactorizeId` at CANONICAL (firing-block) granularity.

## What STAYS WALLED (no flip of the masters)

This flips the r19 `id`-arm residual (recorded additively by `fxAmalg_hasIdCanonicalCollapse`; the r19 marker
`fxAmalg_idCanonicalCollapseStaysGated` keeps its intact home value).  It does NOT ship the whisker junction merge
(arm b, r21) or the vcomp common-refinement zip (arm c = JAM A + fib-3, cross-lane hostage).
`fxAmalg_whiskerJunctionMergeStaysWalled` / `fxAmalg_vcompCommonRefinementZipStaysWalled` /
`fxAmalg_topFactorizationInductionStaysWalled` STAY `true`; the four masters STAY at their walled values; #2043 does
NOT close.

Raw Lean 4 + Init.  STRUCTURAL on the block list / producer witness; cast threading via `hcomp_castBoundaryRight` +
`castBoundaryCongr` + `castBoundary_trans` (all propext-safe).  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The per-block cons collapse (cast-threaded) -/

/-- **The per-block identity-collapse cons step.**  Given the tail collapse `gapVcompLayout finalWall rest ≈
castBoundary rfl restEq (id (gapDomLayout finalWall rest))`, prepending an `idBlockPair wall gap` collapses the head
block: fold `vcomp (id gap) (id gap) ≈ id gap` (`vcompIdLeft`), thread the tail cast out of the inner `hcomp`
(`hcomp_castBoundaryRight`), fold `hcomp (id gap) (id …) ≈ id (gap · …)` (`hcompId_conv_idComposite`) under the cast
(`castBoundaryCongr`), then repeat once for the leading `id wall`.  The result cast is the tail cast wrapped by two
`composePath`s (`congrArg`).  Over ANY signature / base relation. -/
theorem idBlockPairConsVcompCollapse {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (finalWall wall gap : ModalityPath signature.graph oneMode oneMode)
    (rest : List (VcompGapPair signature oneMode))
    (restEq : gapDomLayout finalWall rest = gapCodLayout finalWall rest)
    (restConv : SaturatedConvOver signature baseRel
      (gapVcompLayout finalWall rest)
      (RawTwoCellExpr.castBoundary rfl restEq (RawTwoCellExpr.id (gapDomLayout finalWall rest)))) :
    SaturatedConvOver signature baseRel
      (gapVcompLayout finalWall (idBlockPair wall gap :: rest))
      (RawTwoCellExpr.castBoundary rfl
        (congrArg (fun tailCod => composePath wall (composePath gap tailCod)) restEq)
        (RawTwoCellExpr.id (composePath wall (composePath gap (gapDomLayout finalWall rest))))) := by
  show SaturatedConvOver signature baseRel
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.id wall)
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp (RawTwoCellExpr.id gap) (RawTwoCellExpr.id gap))
          (gapVcompLayout finalWall rest)))
      (RawTwoCellExpr.castBoundary rfl
        (congrArg (fun tailCod => composePath wall (composePath gap tailCod)) restEq)
        (RawTwoCellExpr.id (composePath wall (composePath gap (gapDomLayout finalWall rest)))))
  -- inner: hcomp (vcomp (id gap)(id gap)) (V rest) collapses to castBoundary rfl (composePath gap · restEq) (id (gap·Dt))
  have innerConv : SaturatedConvOver signature baseRel
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp (RawTwoCellExpr.id gap) (RawTwoCellExpr.id gap))
        (gapVcompLayout finalWall rest))
      (RawTwoCellExpr.castBoundary rfl (congrArg (composePath gap) restEq)
        (RawTwoCellExpr.id (composePath gap (gapDomLayout finalWall rest)))) := by
    have stepFold : SaturatedConvOver signature baseRel
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp (RawTwoCellExpr.id gap) (RawTwoCellExpr.id gap))
          (gapVcompLayout finalWall rest))
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.id gap)
          (RawTwoCellExpr.castBoundary rfl restEq (RawTwoCellExpr.id (gapDomLayout finalWall rest)))) :=
      SaturatedConvOver.hcompCongr
        (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id gap))))
        restConv
    rw [RawTwoCellExpr.hcomp_castBoundaryRight rfl restEq (RawTwoCellExpr.id gap)
        (RawTwoCellExpr.id (gapDomLayout finalWall rest))] at stepFold
    refine SaturatedConvOver.trans stepFold ?_
    exact SaturatedConvOver.castBoundaryCongr (congrArg (composePath gap) rfl) (congrArg (composePath gap) restEq)
      (hcompId_conv_idComposite gap (gapDomLayout finalWall rest))
  -- outer: hcomp (id wall) (inner) collapses
  have outerConv : SaturatedConvOver signature baseRel
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.id wall)
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp (RawTwoCellExpr.id gap) (RawTwoCellExpr.id gap))
          (gapVcompLayout finalWall rest)))
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.id wall)
        (RawTwoCellExpr.castBoundary rfl (congrArg (composePath gap) restEq)
          (RawTwoCellExpr.id (composePath gap (gapDomLayout finalWall rest))))) :=
    SaturatedConvOver.hcompCongrRight (RawTwoCellExpr.id wall) innerConv
  refine SaturatedConvOver.trans outerConv ?_
  rw [RawTwoCellExpr.hcomp_castBoundaryRight rfl (congrArg (composePath gap) restEq) (RawTwoCellExpr.id wall)
      (RawTwoCellExpr.id (composePath gap (gapDomLayout finalWall rest)))]
  exact SaturatedConvOver.castBoundaryCongr (congrArg (composePath wall) rfl)
    (congrArg (composePath wall) (congrArg (composePath gap) restEq))
    (hcompId_conv_idComposite wall (composePath gap (gapDomLayout finalWall rest)))

/-- A layout block list is **all-identity** when every block is an `idBlockPair` (a leading wall plus a gap whose
domain / middle / codomain coincide and whose payloads are identities).  The coarse firing-block producer emits
exactly such lists; this predicate lets the identity collapse recurse on the LIST structure (no producer `bif`). -/
inductive AllIdBlocks {signature : ModeSignature} {oneMode : signature.graph.Mode} :
    List (VcompGapPair signature oneMode) → Prop where
  | nil : AllIdBlocks []
  | cons (wall gap : ModalityPath signature.graph oneMode oneMode)
      (rest : List (VcompGapPair signature oneMode)) :
      AllIdBlocks rest → AllIdBlocks (idBlockPair wall gap :: rest)

/-- For an all-identity block list the domain and codomain boundary layouts coincide (every block reads its gap the
same way on both faces).  Structural on the `AllIdBlocks` witness. -/
theorem allIdBlocks_gapDomEqCod {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) → AllIdBlocks pairs →
    gapDomLayout finalWall pairs = gapCodLayout finalWall pairs
  | _, AllIdBlocks.nil => rfl
  | _, AllIdBlocks.cons wall gap rest hrest =>
      congrArg (fun tailCod => composePath wall (composePath gap tailCod))
        (allIdBlocks_gapDomEqCod finalWall rest hrest)

/-- ★★★ **THE IDENTITY-LAYOUT COLLAPSE (list form).**  The vcomp cell layout of an all-identity block list is
saturated-convertible to the identity on its domain 1-cell, up to the `gapDomLayout = gapCodLayout` boundary cast.
Structural on the `AllIdBlocks` witness: `[]` is `refl`; each `idBlockPair` cons fires the per-block collapse
(`idBlockPairConsVcompCollapse`) threading the tail collapse through the two `composePath` cast pushes. -/
theorem gapVcompLayoutIdBlocksCollapse {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) → (allId : AllIdBlocks pairs) →
    SaturatedConvOver signature baseRel
      (gapVcompLayout finalWall pairs)
      (RawTwoCellExpr.castBoundary rfl (allIdBlocks_gapDomEqCod finalWall pairs allId)
        (RawTwoCellExpr.id (gapDomLayout finalWall pairs)))
  | _, AllIdBlocks.nil => SaturatedConvOver.refl _
  | _, AllIdBlocks.cons wall gap rest hrest =>
      idBlockPairConsVcompCollapse finalWall wall gap rest
        (allIdBlocks_gapDomEqCod finalWall rest hrest)
        (gapVcompLayoutIdBlocksCollapse finalWall rest hrest)

/-- The coarse firing-block producer accumulator emits an all-identity block list.  Structural on the path
(Prop-valued, so the producer `bif` splits cleanly): `.nil` emits the single trailing `idBlockPair`; the `t`-gap
case threads the IH with the widened gap; the `s`-wall case conses one `idBlockPair` onto the reset-accumulator IH. -/
theorem firingBlockLayoutAux_allIdBlocks
    (pendingWall currentGap :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    AllIdBlocks (firingBlockLayoutAux pendingWall currentGap path)
  | _, _, .nil _ =>
      AllIdBlocks.cons (signature := involutionMonadPushout.toModeSignature) (oneMode := monadPushMode)
        pendingWall currentGap [] AllIdBlocks.nil
  | _, _, .cons letter rest => by
      show AllIdBlocks
          (bif letterTag involutionMonadSplit letter.val then
            idBlockPair pendingWall currentGap ::
              firingBlockLayoutAux (pushoutEndoPathOfWord [letter.val])
                (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest
          else
            firingBlockLayoutAux pendingWall
              (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest)
      cases hTag : letterTag involutionMonadSplit letter.val with
      | false =>
          exact firingBlockLayoutAux_allIdBlocks pendingWall
            (composePath currentGap (pushoutEndoPathOfWord [letter.val])) rest
      | true =>
          exact AllIdBlocks.cons pendingWall currentGap _
            (firingBlockLayoutAux_allIdBlocks (pushoutEndoPathOfWord [letter.val])
              (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) rest)

/-- ★★★ **THE IDENTITY-LAYOUT COLLAPSE (producer form).**  The vcomp cell layout of the coarse firing-block
producer on an endo path collapses to the identity on its domain layout, up to the `gapDomLayout = gapCodLayout`
boundary cast — the multi-block identity-layout collapse the r19 `id` arm named as its residual.  Assembled from the
list-form collapse (`gapVcompLayoutIdBlocksCollapse`) fed the producer's all-identity witness
(`firingBlockLayoutAux_allIdBlocks`); the cast proof matches `firingBlockLayoutAux_gapDomEqCod` by proof
irrelevance. -/
theorem firingBlockLayoutIdCollapse
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (gapVcompLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (firingBlockLayout path))
      (RawTwoCellExpr.castBoundary rfl
        (firingBlockLayoutAux_gapDomEqCod
          (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) path)
        (RawTwoCellExpr.id (gapDomLayout
          (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (firingBlockLayout path)))) :=
  gapVcompLayoutIdBlocksCollapse
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
    (firingBlockLayout path)
    (firingBlockLayoutAux_allIdBlocks
      (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
      (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) path)

/-! ## The `id`-arm canonical factorization -/

/-- Re-anchor a doubly-cast identity to a single codomain cast: `castBoundary hDom hCod (id sourcePath) =
castBoundary rfl (hDom.symm.trans hCod) (id sourcePath')`.  `cases hDom` collapses the domain cast to `rfl`; the
codomain cast reassociates by proof irrelevance.  The bridge from the factorization's `(domEq, codEq)` boundary casts
to the `firingBlockLayoutIdCollapse` cast form. -/
theorem castBoundaryIdReassoc {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hDom : sourcePath = sourcePath') (hCod : sourcePath = targetPath') :
    RawTwoCellExpr.castBoundary hDom hCod (RawTwoCellExpr.id sourcePath)
      = RawTwoCellExpr.castBoundary rfl (hDom.symm.trans hCod) (RawTwoCellExpr.id sourcePath') := by
  cases hDom; rfl

/-- ★★★ **THE `id` ARM (general, ✅) — an identity 2-cell factors as its coarse firing-block layout.**  For an
arbitrary endo 1-cell `path`, `RawTwoCellExpr.id path` has a `PushoutLayoutFactorization` with `pairs =
firingBlockLayout path` (the coarse producer, one slot per maximal `t`-run): the boundary casts are the B2 round-trips
(`gapDomLayout_firingBlockLayout` / `gapCodLayout_firingBlockLayout`), and the convertibility is the multi-block
identity collapse `firingBlockLayoutIdCollapse` re-anchored by `castBoundaryIdReassoc`.  Supersedes the nil-only
`pushoutFactorizeId` (which places the whole cell in ONE empty slot) at CANONICAL granularity. -/
def pushoutFactorizeIdCanonical
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    PushoutLayoutFactorization crossPairRealPushoutRel (RawTwoCellExpr.id path) where
  finalWall := ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode
  pairs := firingBlockLayout path
  domEq := (gapDomLayout_firingBlockLayout path).symm
  codEq := (gapCodLayout_firingBlockLayout path).symm
  conv := by
    rw [castBoundaryIdReassoc (gapDomLayout_firingBlockLayout path).symm
        (gapCodLayout_firingBlockLayout path).symm]
    exact SaturatedConvOver.symm (firingBlockLayoutIdCollapse path)

/-- ★★★ **THE `id` ARM as a `CanonicalFactorization`.**  `pushoutFactorizeIdCanonical` meets the canonical
firing-block slot count `(finestGapWidths (pushoutPathTags path)).length` by construction (B2's
`firingBlockLayout_slotCount`), so it lifts to the `CanonicalFactorization` subtype — the general `id` arm of the
canonical reader, no longer gated. -/
def idCanonicalFactorization
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    CanonicalFactorization (RawTwoCellExpr.id path) :=
  ⟨pushoutFactorizeIdCanonical path, firingBlockLayout_slotCount path⟩

/-- ★★ **PROBE — the `id` canonical factorization on the r8 wall-splitter reads THREE slots.**  On the all-wall
degenerate boundary `s·s` (`unitSplitsWallDom`), the general `id` arm produces the three-slot firing-block layout
(`(idCanonicalFactorization unitSplitsWallDom).1.pairs.length = 3`, `rfl`) — a leading empty gap, one per wall, a
trailing empty gap — matching the finest slot count on the very word that refuted the wall-BLOCK strategy.  A
genuinely multi-slot `id`-arm inhabitant. -/
theorem idCanonicalFactorizationSlotCount :
    (idCanonicalFactorization unitSplitsWallDom).1.pairs.length = 3 := rfl

/-! ## Observability -/

-- The general `id`-arm slot count on the r8 wall-splitter `s·s` (expect `3`); on the all-gap `t·t` (expect `1`).
#eval (idCanonicalFactorization unitSplitsWallDom).1.pairs.length
#eval (idCanonicalFactorization (composePath monadPushTPath monadPushTPath)).1.pairs.length

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the multi-block identity-layout COLLAPSE conv + the general `id`-arm canonical
factorization SHIP (WP-AMALG-2 r20, B2, arm (a)).**  `= true`.  `firingBlockLayoutIdCollapse` discharges the r19-named
residual: `gapVcompLayout nil (firingBlockLayout path)` is saturated-convertible to the identity on its domain layout,
up to the `gapDomLayout = gapCodLayout` boundary cast — the per-block `vcompIdLeft` + `hcompId_conv_idComposite`
collapse threaded through the cast (`hcomp_castBoundaryRight` + `castBoundaryCongr`), decoupled from the producer
`bif` via the `AllIdBlocks` predicate.  On top of it, `pushoutFactorizeIdCanonical` gives the GENERAL `id` arm
(`PushoutLayoutFactorization crossPairRealPushoutRel (id path)`, `pairs = firingBlockLayout path`, B2 round-trip
casts, `castBoundaryIdReassoc` reconciliation), and `idCanonicalFactorization` lifts it to the `CanonicalFactorization`
subtype (`firingBlockLayout_slotCount`).  Non-vacuous multi-slot: on the r8 wall-splitter `s·s` the general `id` arm
reads THREE slots (`idCanonicalFactorizationSlotCount`, `rfl`).

This is the recon's mechanical arm (a).  It does NOT ship arm (b) (whisker junction merge, r21) or arm (c) (the vcomp
common-refinement zip = JAM A + fib-3, cross-lane hostage).  `fxAmalg_whiskerJunctionMergeStaysWalled` /
`fxAmalg_vcompCommonRefinementZipStaysWalled` / `fxAmalg_topFactorizationInductionStaysWalled` STAY `true`; the four
masters STAY at their walled values; #2043 does NOT close.  `= true`. -/
def fxAmalg_hasIdCanonicalCollapse : Bool := true

/-- ★★★ **The r19 `id`-arm residual node stays at its intact home value; the collapse ships additively (`rfl`).**  r19
held `fxAmalg_idCanonicalCollapseStaysGated = true` naming the multi-block identity-layout collapse conv as the `id`
arm's deferred residual; B2 arm (a) AUTHORS that collapse (`firingBlockLayoutIdCollapse`) and the general `id` arm
(`pushoutFactorizeIdCanonical`), SUPERSEDING the r19 residual with `fxAmalg_hasIdCanonicalCollapse`.  The r19 marker's
home value is left byte-intact (additive, historical); this records that node at its intact `true` and confirms the
masters stay walled — the `id` collapse ships but the two remaining arms (whisker junction merge, vcomp zip) and the
top-level reader do not.  Machine-checked. -/
theorem idCanonicalCollapseShipsResidual :
    fxAmalg_idCanonicalCollapseStaysGated = true
      ∧ fxAmalg_whiskerJunctionMergeStaysWalled = true
      ∧ fxAmalg_vcompCommonRefinementZipStaysWalled = true
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true
      ∧ fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasSaturatedDispatchTheorem = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph.Amalgam
