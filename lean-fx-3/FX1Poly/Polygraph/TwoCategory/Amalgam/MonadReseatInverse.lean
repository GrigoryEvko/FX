import FX1Poly.Polygraph.TwoCategory.Amalgam.MonadReseat
import FX1Poly.Polygraph.TwoCategory.Amalgam.DeciderReseat

/-! # Polygraph/TwoCategory/Amalgam/MonadReseatInverse — the INVERSE reseat functor (bespoke ==> reconstructed)
and the reseated reconstructed-signature decider (MODE-ADMIT-INV r1)

`MonadReseat.lean` (MODE-ADMIT r3/r4) shipped the FORWARD reseat `(reconstructed ==> bespoke)`: the 1-cell functor
`reseatPath`, the crux generator translation `reseatGen`, the free 2-cell functor `reseatCell`, and the forward
CONV transport `reseatConvForward` — thereby the isFalse leg of a reconstructed-signature decision literally
(`monadReconRefutes`).  The r4 honesty marker `fxAmalg_hasReconstructionDecoderReseat = false` named the residual
for the FULL two-sided decider: the isTrue leg needs the BACKWARD (inverse) functor plus the round-trip.

This file builds the INVERSE functor `(bespoke ==> reconstructed)`, the exact structural MIRROR of the forward,
and assembles the reseated reconstructed-signature decision:

  * **`reseatPathInv`** — the inverse 1-cell functor: a bespoke `t`-power `monadT^n` maps to the reconstructed
    `t`-power by COUNTING length (`nil` to `nil`, `cons` to `cons (the single reconstructed generator)`).  It is a
    monoid homomorphism (`reseatPathInv_composePath`), and inverse to `reseatPath` on the mono-mode fibre
    (`reseatPathInv_reseatPath` / `reseatPath_reseatPathInv`).
  * **`reseatGenInv`** — the inverse generator map: bespoke `eta` to the reconstructed unit, `mu` to the
    reconstructed multiplication.  DIRECT (no codomain read, unlike the forward `reseatGen`) because the bespoke
    generator boundaries are CONCRETE and their `reseatPathInv` images DEFINITIONALLY equal the reconstructed
    generator boundaries.
  * **`reseatCellInv`** — the inverse free 2-cell functor, the arm-for-arm mirror of `reseatCell` with
    `reseatPathInv` / `reseatPathInv_composePath` / `reseatGenInv` swapped in; plus its per-constructor reduction
    lemmas.
  * **`reseatCellInv_preservesConv`** — the thirteen-constructor `TwoCellConvFull` functoriality mirror of
    `reseatCell_preservesConv`; `reseatConvBackward` (`recInto` into the `reseatCellInv`-image congruence), the
    BACKWARD conv transport; the three backward law rows (`reconLeftUnitConvBackward` etc.).
  * **`monadReconstructedDecision`** — the reseated decider over `monadComputad.toModeSignature`
    `MonadLawRelReconstructed`, assembled from the bespoke `monadSaturatedTwoCellDecision` via
    `monadSaturated_iff_generic`: isFalse leg via `monadReconRefutes` (forward, roundtrip-free), isTrue leg via
    `reseatConvBackward` + the cell round-trip `reseatCellInv_reseatCell`.

The cast toolkit (B1) is REUSED unchanged from `MonadReseat.lean`'s signature-generic `ReseatCastKit` (the
`eqToHom`-style closed algebra: `refl` / `trans` fusion / `map` push-through / naturality), imported here — a
no-op, per the lit-stage discipline.

Every declaration is `Eq.rec`-only, no `HEq`, fib-3-DECOUPLED (no 2-cell equality modulo the 3-cell laws is
decided — the bespoke decider does that; the inverse only re-bases signatures).  Raw Lean 4 + Init.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## B2 — the inverse 1-cell functor: bespoke `t`-powers ==> reconstructed `t`-powers -/

/-- ★ **The inverse reseat 1-cell functor** — a bespoke monad path `t^n` (over `monadGraph`, one mode / one
endo-generator `t`) maps to the reconstructed `t`-power (over `monadComputad.toModeGraph`, one mode `⟨0⟩` / one
endo-generator `⟨⟨0⟩, rfl⟩`) by COUNTING length: `nil` to `nil ⟨0⟩`, `cons` to `cons` the single reconstructed
generator, ignoring the (constant, single-inhabitant) `MonadMode` / `MonadModality` data.  Takes GENERAL
`MonadMode` endpoints (only `point`), outputs the FIXED `⟨0⟩` endpoints — the mirror of the forward `reseatPath`
(Fin 1 in, fixed `point` out).  Reduces DEFINITIONALLY on `monadT` (`reseatPathInv monadT` DEFEQ
`monadComputadReconstructedT`) — the key to the DIRECT inverse generator map. -/
def reseatPathInv {sourceMode targetMode : MonadMode}
    (path : ModalityPath monadGraph sourceMode targetMode) :
    ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1) :=
  match path with
  | ModalityPath.nil _ => ModalityPath.nil (graph := monadComputad.toModeGraph) ⟨0, by decide⟩
  | ModalityPath.cons _ rest =>
      ModalityPath.cons
        (⟨⟨0, by decide⟩, rfl⟩ : monadComputad.Modality (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1))
        (reseatPathInv rest)

/-- Smoke: the bespoke identity path at `point` maps to the reconstructed identity path (`rfl`). -/
theorem reseatPathInv_nil :
    reseatPathInv (ModalityPath.nil (graph := monadGraph) MonadMode.point)
      = ModalityPath.nil (graph := monadComputad.toModeGraph) (⟨0, by decide⟩ : Fin 1) := rfl

/-- ★ Smoke: the bespoke `monadT` maps to the reconstructed `monadComputadReconstructedT` (`rfl` — the generator
embedding lines up definitionally, the DIRECT-inverse handle). -/
theorem reseatPathInv_monadT : reseatPathInv monadT = monadComputadReconstructedT := rfl

/-- ★ Smoke: the bespoke `monadTThenT` maps to the reconstructed `monadComputadReconstructedTT` (`rfl`). -/
theorem reseatPathInv_monadTThenT : reseatPathInv monadTThenT = monadComputadReconstructedTT := rfl

/-- ★ **`reseatPathInv` is a monoid homomorphism** — it distributes over bespoke path composition
(PROPOSITIONALLY: `composePath` recurses on its first argument, base `rfl`, `cons` step `congrArg`).  The inverse
mirror of `reseatPath_composePath`, threaded through `castBoundary` by the two whisker cases of `reseatCellInv`. -/
theorem reseatPathInv_composePath :
    {sourceMode middleMode targetMode : MonadMode} →
    (first : ModalityPath monadGraph sourceMode middleMode) →
    (second : ModalityPath monadGraph middleMode targetMode) →
    reseatPathInv (composePath first second)
      = composePath (reseatPathInv first) (reseatPathInv second)
  | _, _, _, ModalityPath.nil _, _ => rfl
  | _, _, _, ModalityPath.cons _ rest, second =>
      show ModalityPath.cons (graph := monadComputad.toModeGraph)
            (⟨⟨0, by decide⟩, rfl⟩ : monadComputad.Modality (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1))
            (reseatPathInv (composePath rest second))
          = ModalityPath.cons (graph := monadComputad.toModeGraph)
              (⟨⟨0, by decide⟩, rfl⟩ : monadComputad.Modality (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1))
              (composePath (reseatPathInv rest) (reseatPathInv second)) from
        congrArg
          (ModalityPath.cons (graph := monadComputad.toModeGraph)
            (⟨⟨0, by decide⟩, rfl⟩ : monadComputad.Modality (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1)))
          (reseatPathInv_composePath rest second)

/-! ## B2 — the two round-trips of the mono-mode 1-cell fibre -/

/-- ★ **Round-trip (bespoke start)** — `reseatPath . reseatPathInv = id` on bespoke `t`-powers: counting length
forward then back is the identity (`nil` to `nil`, `cons` step `congrArg`, the single `MonadModality` inversion
`MonadModality.t` matched explicitly).  The `cons` modality is drawn by explicit match (propext-free). -/
theorem reseatPath_reseatPathInv :
    (path : ModalityPath monadGraph MonadMode.point MonadMode.point) → reseatPath (reseatPathInv path) = path
  | ModalityPath.nil _ => rfl
  | ModalityPath.cons MonadModality.t rest =>
      congrArg (ModalityPath.cons (graph := monadGraph) MonadModality.t) (reseatPath_reseatPathInv rest)

/-! ## B3 — the inverse generator translation + the inverse free 2-cell functor -/

/-- ★★ **The inverse generator translation** — a bespoke `MonadTwoCell` maps to the reconstructed 2-generator at
the `reseatPathInv`-image boundary.  `eta` to the reconstructed unit `monadComputadReconstructsUnit`, `mu` to the
reconstructed multiplication `monadComputadReconstructsMult`.  DIRECT — unlike the forward `reseatGen` (which
reads the codomain through interpreter witnesses), the bespoke generator boundaries `(nil point, monadT)` /
`(monadTThenT, monadT)` are CONCRETE and their `reseatPathInv` images DEFINITIONALLY equal the reconstructed
generator boundaries `(nil ⟨0⟩, t)` / `(t·t, t)`, so no boundary cast is needed. -/
def reseatGenInv : {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    MonadTwoCell sourcePath targetPath →
    monadComputad.ReconstructedTwoCell (reseatPathInv sourcePath) (reseatPathInv targetPath)
  | _, _, _, _, MonadTwoCell.eta => monadComputadReconstructsUnit
  | _, _, _, _, MonadTwoCell.mu => monadComputadReconstructsMult

/-- Smoke: `reseatGenInv` on the bespoke unit IS the reconstructed unit (`rfl`). -/
theorem reseatGenInv_eta : reseatGenInv MonadTwoCell.eta = monadComputadReconstructsUnit := rfl

/-- Smoke: `reseatGenInv` on the bespoke multiplication IS the reconstructed multiplication (`rfl`). -/
theorem reseatGenInv_mu : reseatGenInv MonadTwoCell.mu = monadComputadReconstructsMult := rfl

/-- ★★ **The inverse reseat cell functor** — lift `reseatGenInv` over the whole `RawTwoCellExpr` grammar: a bespoke
free 2-cell over `monadModeSignature` transports to a reconstructed free 2-cell over
`monadComputad.toModeSignature`, boundaries carried by `reseatPathInv`.  The arm-for-arm structural MIRROR of
`reseatCell`: `gen` via `reseatGenInv`; `id` / `vcomp` cast-free; the two whisker cases through the single
`castBoundary (reseatPathInv_composePath ..)`. -/
def reseatCellInv {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    RawTwoCellExpr monadComputad.toModeSignature (reseatPathInv sourcePath) (reseatPathInv targetPath) :=
  match cell with
  | RawTwoCellExpr.gen generator => RawTwoCellExpr.gen (reseatGenInv generator)
  | RawTwoCellExpr.id path =>
      RawTwoCellExpr.id (signature := monadComputad.toModeSignature) (reseatPathInv path)
  | RawTwoCellExpr.vcomp cellAlpha cellBeta =>
      RawTwoCellExpr.vcomp (reseatCellInv cellAlpha) (reseatCellInv cellBeta)
  | @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell oneCellG oneCellH body =>
      RawTwoCellExpr.castBoundary
        (reseatPathInv_composePath oneCell oneCellG).symm
        (reseatPathInv_composePath oneCell oneCellH).symm
        (RawTwoCellExpr.whiskerLeft (reseatPathInv oneCell) (reseatCellInv body))
  | @RawTwoCellExpr.whiskerRight _ _ _ _ oneCellF oneCellG oneCell body =>
      RawTwoCellExpr.castBoundary
        (reseatPathInv_composePath oneCellF oneCell).symm
        (reseatPathInv_composePath oneCellG oneCell).symm
        (RawTwoCellExpr.whiskerRight (reseatPathInv oneCell) (reseatCellInv body))

/-- Smoke: `reseatCellInv` on a bare generator IS `gen (reseatGenInv ..)` (`rfl`). -/
theorem reseatCellInv_gen {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (generator : MonadTwoCell sourcePath targetPath) :
    reseatCellInv (RawTwoCellExpr.gen generator) = RawTwoCellExpr.gen (reseatGenInv generator) := rfl

/-- ★ `reseatCellInv` of the bespoke unit IS the reconstructed unit 2-cell `reconEta` (`rfl` — `reseatGenInv` is
DIRECT, cleaner than the forward's non-`rfl` `reseatCell_reconEta`). -/
theorem reseatCellInv_monadUnit : reseatCellInv monadUnitTwoCell = reconEta := rfl

/-- ★ `reseatCellInv` of the bespoke multiplication IS the reconstructed multiplication 2-cell `reconMu` (`rfl`). -/
theorem reseatCellInv_monadMul : reseatCellInv monadMulTwoCell = reconMu := rfl

/-- `reseatCellInv` of the bespoke identity 2-cell IS the reconstructed identity 2-cell `reconIdTCell` (`rfl`). -/
theorem reseatCellInv_monadIdT : reseatCellInv monadIdTCell = reconIdTCell := rfl

/-! ## B3 — `reseatCellInv` per-constructor reduction lemmas (mirror of `reseatCell_*`) -/

/-- `reseatCellInv` on an identity 2-cell (`rfl`). -/
theorem reseatCellInv_id {sourceMode targetMode : MonadMode}
    (path : ModalityPath monadGraph sourceMode targetMode) :
    reseatCellInv (RawTwoCellExpr.id path)
      = RawTwoCellExpr.id (signature := monadComputad.toModeSignature) (reseatPathInv path) := rfl

/-- `reseatCellInv` on a vertical composite (`rfl`, cast-free). -/
theorem reseatCellInv_vcomp {sourceMode targetMode : MonadMode}
    {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr monadModeSignature oneCellG oneCellH) :
    reseatCellInv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = RawTwoCellExpr.vcomp (reseatCellInv cellAlpha) (reseatCellInv cellBeta) := rfl

/-- `reseatCellInv` on a left whiskering — the single `reseatPathInv_composePath` cast (`rfl`). -/
theorem reseatCellInv_whiskerLeft {sourceMode middleMode targetMode : MonadMode}
    (oneCell : ModalityPath monadGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath monadGraph middleMode targetMode}
    (body : RawTwoCellExpr monadModeSignature oneCellG oneCellH) :
    reseatCellInv (RawTwoCellExpr.whiskerLeft oneCell body)
      = RawTwoCellExpr.castBoundary
          (reseatPathInv_composePath oneCell oneCellG).symm
          (reseatPathInv_composePath oneCell oneCellH).symm
          (RawTwoCellExpr.whiskerLeft (reseatPathInv oneCell) (reseatCellInv body)) := rfl

/-- `reseatCellInv` on a right whiskering — the single `reseatPathInv_composePath` cast (`rfl`). -/
theorem reseatCellInv_whiskerRight {sourceMode middleMode targetMode : MonadMode}
    {oneCellF oneCellG : ModalityPath monadGraph sourceMode middleMode}
    (oneCell : ModalityPath monadGraph middleMode targetMode)
    (body : RawTwoCellExpr monadModeSignature oneCellF oneCellG) :
    reseatCellInv (RawTwoCellExpr.whiskerRight oneCell body)
      = RawTwoCellExpr.castBoundary
          (reseatPathInv_composePath oneCellF oneCell).symm
          (reseatPathInv_composePath oneCellG oneCell).symm
          (RawTwoCellExpr.whiskerRight (reseatPathInv oneCell) (reseatCellInv body)) := rfl

/-- `reseatCellInv` commutes with `castBoundary` (both `Eq.rec`; `cases` the equalities). -/
theorem reseatCellInv_castBoundary {sourceMode targetMode : MonadMode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadGraph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    reseatCellInv (RawTwoCellExpr.castBoundary hsource htarget cell)
      = RawTwoCellExpr.castBoundary (congrArg reseatPathInv hsource) (congrArg reseatPathInv htarget)
          (reseatCellInv cell) := by
  cases hsource; cases htarget; rfl

/-- `reseatCellInv` commutes with the derived Godement product `hcomp` up to one boundary cast. -/
theorem reseatCellInv_hcomp {sourceMode middleMode targetMode : MonadMode}
    {oneCellFDom oneCellFCod : ModalityPath monadGraph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath monadGraph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr monadModeSignature oneCellFDom oneCellFCod)
    (cellBeta : RawTwoCellExpr monadModeSignature oneCellGDom oneCellGCod) :
    reseatCellInv (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      = RawTwoCellExpr.castBoundary
          (reseatPathInv_composePath oneCellFDom oneCellGDom).symm
          (reseatPathInv_composePath oneCellFCod oneCellGCod).symm
          (RawTwoCellExpr.hcomp (reseatCellInv cellAlpha) (reseatCellInv cellBeta)) := by
  show RawTwoCellExpr.vcomp (reseatCellInv (RawTwoCellExpr.whiskerRight oneCellGDom cellAlpha))
      (reseatCellInv (RawTwoCellExpr.whiskerLeft oneCellFCod cellBeta)) = _
  exact (ReseatCastKit.castBoundaryVcomp
    (reseatPathInv_composePath oneCellFDom oneCellGDom).symm
    (reseatPathInv_composePath oneCellFCod oneCellGDom).symm
    (reseatPathInv_composePath oneCellFCod oneCellGCod).symm
    (RawTwoCellExpr.whiskerRight (reseatPathInv oneCellGDom) (reseatCellInv cellAlpha))
    (RawTwoCellExpr.whiskerLeft (reseatPathInv oneCellFCod) (reseatCellInv cellBeta))).symm

/-- `reseatCellInv` through `whiskerLeft . whiskerLeft`. -/
theorem reseatCellInv_whiskerLeft_whiskerLeft {sm mm1 mm2 tm : MonadMode}
    (oneCellOuter : ModalityPath monadGraph sm mm1)
    (oneCellInner : ModalityPath monadGraph mm1 mm2)
    {bodyDom bodyCod : ModalityPath monadGraph mm2 tm}
    (body : RawTwoCellExpr monadModeSignature bodyDom bodyCod) :
    reseatCellInv (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (composePath (reseatPathInv oneCellOuter))
              (reseatPathInv_composePath oneCellInner bodyDom).symm).trans
            (reseatPathInv_composePath oneCellOuter (composePath oneCellInner bodyDom)).symm)
          ((congrArg (composePath (reseatPathInv oneCellOuter))
              (reseatPathInv_composePath oneCellInner bodyCod).symm).trans
            (reseatPathInv_composePath oneCellOuter (composePath oneCellInner bodyCod)).symm)
          (RawTwoCellExpr.whiskerLeft (reseatPathInv oneCellOuter)
            (RawTwoCellExpr.whiskerLeft (reseatPathInv oneCellInner)
              (reseatCellInv body))) :=
  (reseatCellInv_whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerLeft (reseatPathInv oneCellOuter))
            (reseatCellInv_whiskerLeft oneCellInner body)).trans
          (ReseatCastKit.whiskerLeftCastBoundary (reseatPathInv oneCellOuter) _ _
            (RawTwoCellExpr.whiskerLeft (reseatPathInv oneCellInner)
              (reseatCellInv body))))).trans
      (ReseatCastKit.castBoundaryTrans _ _ _ _ _))

/-- `reseatCellInv` through `whiskerRight . whiskerRight`. -/
theorem reseatCellInv_whiskerRight_whiskerRight {sm mm1 mm2 tm : MonadMode}
    {bodyDom bodyCod : ModalityPath monadGraph sm mm1}
    (oneCellInner : ModalityPath monadGraph mm1 mm2)
    (oneCellOuter : ModalityPath monadGraph mm2 tm)
    (body : RawTwoCellExpr monadModeSignature bodyDom bodyCod) :
    reseatCellInv (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (fun path => composePath path (reseatPathInv oneCellOuter))
              (reseatPathInv_composePath bodyDom oneCellInner).symm).trans
            (reseatPathInv_composePath (composePath bodyDom oneCellInner) oneCellOuter).symm)
          ((congrArg (fun path => composePath path (reseatPathInv oneCellOuter))
              (reseatPathInv_composePath bodyCod oneCellInner).symm).trans
            (reseatPathInv_composePath (composePath bodyCod oneCellInner) oneCellOuter).symm)
          (RawTwoCellExpr.whiskerRight (reseatPathInv oneCellOuter)
            (RawTwoCellExpr.whiskerRight (reseatPathInv oneCellInner)
              (reseatCellInv body))) :=
  (reseatCellInv_whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerRight (reseatPathInv oneCellOuter))
            (reseatCellInv_whiskerRight oneCellInner body)).trans
          (ReseatCastKit.whiskerRightCastBoundary (reseatPathInv oneCellOuter) _ _
            (RawTwoCellExpr.whiskerRight (reseatPathInv oneCellInner)
              (reseatCellInv body))))).trans
      (ReseatCastKit.castBoundaryTrans _ _ _ _ _))

/-- `reseatCellInv` through `whiskerLeft . whiskerRight`. -/
theorem reseatCellInv_whiskerLeft_whiskerRight {sm ms mt tm : MonadMode}
    (leftWhisker : ModalityPath monadGraph sm ms)
    {bodyDom bodyCod : ModalityPath monadGraph ms mt}
    (rightWhisker : ModalityPath monadGraph mt tm)
    (body : RawTwoCellExpr monadModeSignature bodyDom bodyCod) :
    reseatCellInv (RawTwoCellExpr.whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (composePath (reseatPathInv leftWhisker))
              (reseatPathInv_composePath bodyDom rightWhisker).symm).trans
            (reseatPathInv_composePath leftWhisker (composePath bodyDom rightWhisker)).symm)
          ((congrArg (composePath (reseatPathInv leftWhisker))
              (reseatPathInv_composePath bodyCod rightWhisker).symm).trans
            (reseatPathInv_composePath leftWhisker (composePath bodyCod rightWhisker)).symm)
          (RawTwoCellExpr.whiskerLeft (reseatPathInv leftWhisker)
            (RawTwoCellExpr.whiskerRight (reseatPathInv rightWhisker)
              (reseatCellInv body))) :=
  (reseatCellInv_whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerLeft (reseatPathInv leftWhisker))
            (reseatCellInv_whiskerRight rightWhisker body)).trans
          (ReseatCastKit.whiskerLeftCastBoundary (reseatPathInv leftWhisker) _ _
            (RawTwoCellExpr.whiskerRight (reseatPathInv rightWhisker)
              (reseatCellInv body))))).trans
      (ReseatCastKit.castBoundaryTrans _ _ _ _ _))

/-- `reseatCellInv` through `whiskerRight . whiskerLeft`. -/
theorem reseatCellInv_whiskerRight_whiskerLeft {sm ms mt tm : MonadMode}
    (leftWhisker : ModalityPath monadGraph sm ms)
    {bodyDom bodyCod : ModalityPath monadGraph ms mt}
    (rightWhisker : ModalityPath monadGraph mt tm)
    (body : RawTwoCellExpr monadModeSignature bodyDom bodyCod) :
    reseatCellInv (RawTwoCellExpr.whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (fun path => composePath path (reseatPathInv rightWhisker))
              (reseatPathInv_composePath leftWhisker bodyDom).symm).trans
            (reseatPathInv_composePath (composePath leftWhisker bodyDom) rightWhisker).symm)
          ((congrArg (fun path => composePath path (reseatPathInv rightWhisker))
              (reseatPathInv_composePath leftWhisker bodyCod).symm).trans
            (reseatPathInv_composePath (composePath leftWhisker bodyCod) rightWhisker).symm)
          (RawTwoCellExpr.whiskerRight (reseatPathInv rightWhisker)
            (RawTwoCellExpr.whiskerLeft (reseatPathInv leftWhisker)
              (reseatCellInv body))) :=
  (reseatCellInv_whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerRight (reseatPathInv rightWhisker))
            (reseatCellInv_whiskerLeft leftWhisker body)).trans
          (ReseatCastKit.whiskerRightCastBoundary (reseatPathInv rightWhisker) _ _
            (RawTwoCellExpr.whiskerLeft (reseatPathInv leftWhisker)
              (reseatCellInv body))))).trans
      (ReseatCastKit.castBoundaryTrans _ _ _ _ _))

end FX1Poly.Polygraph.Amalgam
