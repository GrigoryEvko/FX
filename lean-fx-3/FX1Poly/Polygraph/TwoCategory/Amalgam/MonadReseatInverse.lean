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
    monoid homomorphism (`reseatPathInv_composePath`), and inverse to `reseatPath` on the mono-mode fibre at the
    length level (`reseatPathInv_length`).
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

/-! ## B2 — length faithfulness of the inverse 1-cell functor -/

/-- ★ **`reseatPathInv` preserves length** — it COUNTS length (`nil` to `nil ⟨0⟩`, `cons` to `cons`), so the
reconstructed `t`-power has the same length as the bespoke one.  Polymorphic over the `MonadMode` endpoints
(variable indices, so structural recursion applies), the length-faithfulness witness that `reseatPathInv` is the
honest inverse of `reseatPath` on the mono-mode fibre (both are length-determined over one mode / one generator;
a full path-level `reseatPath . reseatPathInv = id` is blocked by the non-variable-index recursion — drawing the
`cons` middle mode needs a `cases` that breaks structural recursion). -/
theorem reseatPathInv_length : {sourceMode targetMode : MonadMode} →
    (path : ModalityPath monadGraph sourceMode targetMode) →
    (reseatPathInv path).length = path.length
  | _, _, ModalityPath.nil _ => rfl
  | _, _, ModalityPath.cons _ rest => congrArg (fun count => count + 1) (reseatPathInv_length rest)

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

/-! ## B4 — the inverse conv functoriality: `reseatCellInv` preserves the free rewrites, then the completed conv -/

/-- ★ `reseatCellInv` preserves the twelve free 3-cell rewrites — the arm-for-arm inverse mirror of
`reseatTwoCellStep`, with `reseatCellInv` / `reseatPathInv` / `reseatPathInv_composePath` swapped in and the two
signatures exchanged (source `monadModeSignature`, target `monadComputad.toModeSignature`). -/
theorem reseatTwoCellStepInv {sourceMode targetMode : monadModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (step : TwoCellStep monadModeSignature cellAlpha cellBeta) :
    TwoCellConvFull monadComputad.toModeSignature (reseatCellInv cellAlpha) (reseatCellInv cellBeta) := by
  induction step with
  | vcompIdLeft cellA =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (reseatCellInv cellA)))
  | vcompIdRight cellA =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight (reseatCellInv cellA)))
  | vcompAssoc cellA cellB cellC =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc (reseatCellInv cellA) (reseatCellInv cellB) (reseatCellInv cellC)))
  | whiskerLeftId oneCell path =>
      simp only [reseatCellInv_whiskerLeft, reseatCellInv_id]
      exact TwoCellConvFull.trans
        (ReseatCastKit.castBoundaryCongr
          (reseatPathInv_composePath oneCell path).symm
          (reseatPathInv_composePath oneCell path).symm
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (@TwoCellStep.whiskerLeftId monadComputad.toModeSignature _ _ _
              (reseatPathInv oneCell) (reseatPathInv path)))))
        (ReseatCastKit.convFullOfCellEq (ReseatCastKit.castBoundaryId
          (reseatPathInv_composePath oneCell path).symm))
  | whiskerRightId path oneCell =>
      simp only [reseatCellInv_whiskerRight, reseatCellInv_id]
      exact TwoCellConvFull.trans
        (ReseatCastKit.castBoundaryCongr
          (reseatPathInv_composePath path oneCell).symm
          (reseatPathInv_composePath path oneCell).symm
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (@TwoCellStep.whiskerRightId monadComputad.toModeSignature _ _ _
              (reseatPathInv path) (reseatPathInv oneCell)))))
        (ReseatCastKit.convFullOfCellEq (ReseatCastKit.castBoundaryId
          (reseatPathInv_composePath path oneCell).symm))
  | whiskerLeftVcomp oneCell cellB cellC =>
      exact TwoCellConvFull.trans
        (ReseatCastKit.castBoundaryCongr _ _
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (TwoCellStep.whiskerLeftVcomp (reseatPathInv oneCell)
              (reseatCellInv cellB) (reseatCellInv cellC)))))
        (ReseatCastKit.convFullOfCellEq (ReseatCastKit.castBoundaryVcomp _ _ _ _ _))
  | whiskerRightVcomp oneCell cellA cellB =>
      exact TwoCellConvFull.trans
        (ReseatCastKit.castBoundaryCongr _ _
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (TwoCellStep.whiskerRightVcomp (reseatPathInv oneCell)
              (reseatCellInv cellA) (reseatCellInv cellB)))))
        (ReseatCastKit.convFullOfCellEq (ReseatCastKit.castBoundaryVcomp _ _ _ _ _))
  | vcompCongrLeft cellB _ ih =>
      exact TwoCellConvFull.vcompCongrLeft (reseatCellInv cellB) ih
  | vcompCongrRight cellA _ ih =>
      exact TwoCellConvFull.vcompCongrRight (reseatCellInv cellA) ih
  | whiskerLeftCongr oneCell _ ih =>
      exact ReseatCastKit.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerLeftCongr (reseatPathInv oneCell) ih)
  | whiskerRightCongr oneCell _ ih =>
      exact ReseatCastKit.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerRightCongr (reseatPathInv oneCell) ih)
  | interchange cellA cellAUpper cellB cellBUpper =>
      simp only [reseatCellInv_hcomp, reseatCellInv_vcomp]
      refine TwoCellConvFull.trans
        (ReseatCastKit.castBoundaryCongr _ _
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (TwoCellStep.interchange (reseatCellInv cellA) (reseatCellInv cellAUpper)
              (reseatCellInv cellB) (reseatCellInv cellBUpper))))) ?_
      exact ReseatCastKit.convFullOfCellEq (ReseatCastKit.castBoundaryVcomp _ _ _ _ _)

/-- `reseatCellInv` preserves the free `TwoCellConv` closure — inverse mirror of `reseatTwoCellConv`. -/
theorem reseatTwoCellConvInv {sourceMode targetMode : monadModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : TwoCellConv monadModeSignature cellAlpha cellBeta) :
    TwoCellConvFull monadComputad.toModeSignature (reseatCellInv cellAlpha) (reseatCellInv cellBeta) := by
  induction conv with
  | ofStep step => exact reseatTwoCellStepInv step
  | refl cell => exact TwoCellConvFull.refl (reseatCellInv cell)
  | symm _ ih => exact TwoCellConvFull.symm ih
  | trans _ _ ih1 ih2 => exact TwoCellConvFull.trans ih1 ih2

/-- ★★ **B4 linchpin — `reseatCellInv` preserves the COMPLETED convertibility.**  `TwoCellConvFull` over the
bespoke `monadModeSignature` transports along `reseatCellInv` to the reconstructed `monadComputad.toModeSignature`.
The thirteen-constructor structural functoriality, arm-for-arm the inverse mirror of `reseatCell_preservesConv`
(the `ofConv` case reuses `reseatTwoCellConvInv`; the whisker-functoriality laws reconcile `reseatCellInv`'s cast
with the same-named target law through the `ReseatCastKit` cast algebra).  NO arm needs a monad coherence —
`TwoCellConvFull` is law-free, pure cast LABOR. -/
theorem reseatCellInv_preservesConv {sourceMode targetMode : monadModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (convFull : TwoCellConvFull monadModeSignature cellAlpha cellBeta) :
    TwoCellConvFull monadComputad.toModeSignature (reseatCellInv cellAlpha) (reseatCellInv cellBeta) := by
  induction convFull with
  | ofConv conv => exact reseatTwoCellConvInv conv
  | whiskerLeftUnit body => exact TwoCellConvFull.whiskerLeftUnit (reseatCellInv body)
  | whiskerRightUnit body =>
      rename_i sourceMode targetMode oneCellDom oneCellCod
      refine TwoCellConvFull.trans (ReseatCastKit.convFullOfCellEq ?_)
        (TwoCellConvFull.trans
          (ReseatCastKit.castBoundaryCongr
            (reseatPathInv_composePath oneCellDom (identityPath targetMode)).symm
            (reseatPathInv_composePath oneCellCod (identityPath targetMode)).symm
            (TwoCellConvFull.whiskerRightUnit (reseatCellInv body)))
          (ReseatCastKit.convFullOfCellEq ?_))
      · exact reseatCellInv_whiskerRight (identityPath targetMode) body
      · exact (ReseatCastKit.castBoundaryTrans _ _ _ _ _).trans
          (reseatCellInv_castBoundary _ _ body).symm
  | whiskerLeftComp oneCellOuter oneCellInner body =>
      rename_i oneCellDom oneCellCod
      refine TwoCellConvFull.trans (ReseatCastKit.convFullOfCellEq ?_)
        (TwoCellConvFull.trans
          (ReseatCastKit.castBoundaryCongr
            ((congrArg (fun path => composePath path (reseatPathInv oneCellDom))
                (reseatPathInv_composePath oneCellOuter oneCellInner).symm).trans
              (reseatPathInv_composePath (composePath oneCellOuter oneCellInner) oneCellDom).symm)
            ((congrArg (fun path => composePath path (reseatPathInv oneCellCod))
                (reseatPathInv_composePath oneCellOuter oneCellInner).symm).trans
              (reseatPathInv_composePath (composePath oneCellOuter oneCellInner) oneCellCod).symm)
            (TwoCellConvFull.whiskerLeftComp (reseatPathInv oneCellOuter)
              (reseatPathInv oneCellInner) (reseatCellInv body)))
          (ReseatCastKit.convFullOfCellEq ?_))
      · exact (reseatCellInv_whiskerLeft (composePath oneCellOuter oneCellInner) body).trans
          ((congrArg (RawTwoCellExpr.castBoundary _ _)
            (ReseatCastKit.whiskerLeftPathCongr
              (reseatPathInv_composePath oneCellOuter oneCellInner).symm
              (reseatCellInv body))).trans
            (ReseatCastKit.castBoundaryTrans _ _ _ _ _))
      · refine Eq.trans ?_ (reseatCellInv_castBoundary _ _
          (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))).symm
        refine Eq.trans ?_ (congrArg (RawTwoCellExpr.castBoundary _ _)
          (reseatCellInv_whiskerLeft_whiskerLeft oneCellOuter oneCellInner body).symm)
        exact (ReseatCastKit.castBoundaryTrans _ _ _ _ _).trans
          (ReseatCastKit.castBoundaryTrans _ _ _ _ _).symm
  | whiskerRightComp oneCellInner oneCellOuter body =>
      rename_i oneCellDom oneCellCod
      refine TwoCellConvFull.trans (ReseatCastKit.convFullOfCellEq ?_)
        (TwoCellConvFull.trans
          (ReseatCastKit.castBoundaryCongr
            ((congrArg (composePath (reseatPathInv oneCellDom))
                (reseatPathInv_composePath oneCellInner oneCellOuter).symm).trans
              (reseatPathInv_composePath oneCellDom (composePath oneCellInner oneCellOuter)).symm)
            ((congrArg (composePath (reseatPathInv oneCellCod))
                (reseatPathInv_composePath oneCellInner oneCellOuter).symm).trans
              (reseatPathInv_composePath oneCellCod (composePath oneCellInner oneCellOuter)).symm)
            (TwoCellConvFull.whiskerRightComp (reseatPathInv oneCellInner)
              (reseatPathInv oneCellOuter) (reseatCellInv body)))
          (ReseatCastKit.convFullOfCellEq ?_))
      · exact (reseatCellInv_whiskerRight (composePath oneCellInner oneCellOuter) body).trans
          ((congrArg (RawTwoCellExpr.castBoundary _ _)
            (ReseatCastKit.whiskerRightPathCongr
              (reseatPathInv_composePath oneCellInner oneCellOuter).symm
              (reseatCellInv body))).trans
            (ReseatCastKit.castBoundaryTrans _ _ _ _ _))
      · refine Eq.trans ?_ (reseatCellInv_castBoundary _ _
          (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))).symm
        refine Eq.trans ?_ (congrArg (RawTwoCellExpr.castBoundary _ _)
          (reseatCellInv_whiskerRight_whiskerRight oneCellInner oneCellOuter body).symm)
        exact (ReseatCastKit.castBoundaryTrans _ _ _ _ _).trans
          (ReseatCastKit.castBoundaryTrans _ _ _ _ _).symm
  | whiskerExchange leftWhisker rightWhisker body =>
      rename_i bodyDom bodyCod
      refine TwoCellConvFull.trans (ReseatCastKit.convFullOfCellEq ?_)
        (TwoCellConvFull.trans
          (ReseatCastKit.castBoundaryCongr
            ((congrArg (composePath (reseatPathInv leftWhisker))
                (reseatPathInv_composePath bodyDom rightWhisker).symm).trans
              (reseatPathInv_composePath leftWhisker (composePath bodyDom rightWhisker)).symm)
            ((congrArg (composePath (reseatPathInv leftWhisker))
                (reseatPathInv_composePath bodyCod rightWhisker).symm).trans
              (reseatPathInv_composePath leftWhisker (composePath bodyCod rightWhisker)).symm)
            (TwoCellConvFull.whiskerExchange (reseatPathInv leftWhisker)
              (reseatPathInv rightWhisker) (reseatCellInv body)))
          (ReseatCastKit.convFullOfCellEq ?_))
      · exact reseatCellInv_whiskerLeft_whiskerRight leftWhisker rightWhisker body
      · refine Eq.trans ?_ (reseatCellInv_castBoundary _ _
          (RawTwoCellExpr.whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body))).symm
        refine Eq.trans ?_ (congrArg (RawTwoCellExpr.castBoundary _ _)
          (reseatCellInv_whiskerRight_whiskerLeft leftWhisker rightWhisker body).symm)
        exact (ReseatCastKit.castBoundaryTrans _ _ _ _ _).trans
          (ReseatCastKit.castBoundaryTrans _ _ _ _ _).symm
  | vcompCongrLeft cellBeta _ ih => exact TwoCellConvFull.vcompCongrLeft (reseatCellInv cellBeta) ih
  | vcompCongrRight cellAlpha _ ih => exact TwoCellConvFull.vcompCongrRight (reseatCellInv cellAlpha) ih
  | whiskerLeftCongr oneCell _ ih =>
      exact ReseatCastKit.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerLeftCongr (reseatPathInv oneCell) ih)
  | whiskerRightCongr oneCell _ ih =>
      exact ReseatCastKit.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerRightCongr (reseatPathInv oneCell) ih)
  | refl cell => exact TwoCellConvFull.refl (reseatCellInv cell)
  | symm _ ih => exact TwoCellConvFull.symm ih
  | trans _ _ ih1 ih2 => exact TwoCellConvFull.trans ih1 ih2

/-! ## B4 — the three BACKWARD law rows (bespoke law cell ==> reconstructed conv, via the DIRECT generator inversions)

The inverse mirror of `reconLeftUnitConv` / `reconRightUnitConv` / `reconAssocConv`.  Cleaner than the forward: the
generator inversions `reseatCellInv_monadUnit` / `reseatCellInv_monadMul` are `rfl` (the DIRECT `reseatGenInv`),
whereas the forward's `reseatCell_reconEta` / `reseatCell_reconMu` are not.  `reseatCellInv` of a bespoke law
composite reduces DEFINITIONALLY to the reconstructed shape carrying `reseatCellInv`-image generators (the
`castBoundary`s collapse — `reseatPathInv_composePath` on `t`-powers is `rfl`); the generator equalities are lifted
to `TwoCellConvFull` by `convFullOfCellEq` and whiskered / vcomp'd through `SaturatedConvOver`'s congruences to
reach the reconstructed law composite, then chained with the reconstructed `MonadLawRelReconstructed` row. -/

/-- The bespoke left-unit law transports to the reconstructed saturated conv, at the `reseatCellInv`-image
boundary. -/
theorem reconLeftUnitConvBackward :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
      (reseatCellInv monadLeftUnitCell) (reseatCellInv monadIdTCell) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrLeft (reseatCellInv monadMulTwoCell)
        (SaturatedConvOver.whiskerRightCongr monadComputadReconstructedT
          (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCellInv_monadUnit))))
      (SaturatedConvOver.vcompCongrRight
        (RawTwoCellExpr.whiskerRight (signature := monadComputad.toModeSignature)
          monadComputadReconstructedT reconEta)
        (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCellInv_monadMul))))
    (SaturatedConvOver.ofRelation MonadLawRelReconstructed.leftUnit)

/-- The bespoke right-unit law transports to the reconstructed saturated conv. -/
theorem reconRightUnitConvBackward :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
      (reseatCellInv monadRightUnitCell) (reseatCellInv monadIdTCell) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrLeft (reseatCellInv monadMulTwoCell)
        (SaturatedConvOver.whiskerLeftCongr monadComputadReconstructedT
          (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCellInv_monadUnit))))
      (SaturatedConvOver.vcompCongrRight
        (RawTwoCellExpr.whiskerLeft (signature := monadComputad.toModeSignature)
          monadComputadReconstructedT reconEta)
        (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCellInv_monadMul))))
    (SaturatedConvOver.ofRelation MonadLawRelReconstructed.rightUnit)

/-- The bespoke associativity law transports to the reconstructed saturated conv. -/
theorem reconAssocConvBackward :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
      (reseatCellInv monadAssocLeftCell) (reseatCellInv monadAssocRightCell) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.trans
      (SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft (reseatCellInv monadMulTwoCell)
          (SaturatedConvOver.whiskerRightCongr monadComputadReconstructedT
            (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCellInv_monadMul))))
        (SaturatedConvOver.vcompCongrRight
          (RawTwoCellExpr.whiskerRight (signature := monadComputad.toModeSignature)
            monadComputadReconstructedT reconMu)
          (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCellInv_monadMul))))
      (SaturatedConvOver.ofRelation MonadLawRelReconstructed.assoc))
    (SaturatedConvOver.symm
      (SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft (reseatCellInv monadMulTwoCell)
          (SaturatedConvOver.whiskerLeftCongr monadComputadReconstructedT
            (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCellInv_monadMul))))
        (SaturatedConvOver.vcompCongrRight
          (RawTwoCellExpr.whiskerLeft (signature := monadComputad.toModeSignature)
            monadComputadReconstructedT reconMu)
          (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCellInv_monadMul)))))

/-! ## B4 — the BACKWARD conv transport -/

/-- The absorbing congruence for the reseat backward transport — the inverse mirror of `reseatCongruence`:
`ofFull` via `reseatCellInv_preservesConv`; `ofRelation` via the three backward law rows; the two `vcomp`
congruences cast-free; the two `whisker` congruences through `SaturatedConvOver.castBoundaryCongr`;
`refl`/`symm`/`trans` structural. -/
def reseatCongruenceBackward :
    IsSaturatedCongruence monadModeSignature MonadLawRel
      (fun cellA cellB =>
        SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
          (reseatCellInv cellA) (reseatCellInv cellB)) where
  ofFull full := SaturatedConvOver.ofFull (reseatCellInv_preservesConv full)
  ofRelation row :=
    match row with
    | MonadLawRel.leftUnit => reconLeftUnitConvBackward
    | MonadLawRel.rightUnit => reconRightUnitConvBackward
    | MonadLawRel.assoc => reconAssocConvBackward
  vcompCongrLeft {_ _ _ _ _ _ _ cellBeta} ih := SaturatedConvOver.vcompCongrLeft (reseatCellInv cellBeta) ih
  vcompCongrRight {_ _ _ _ _ cellAlpha _ _} ih := SaturatedConvOver.vcompCongrRight (reseatCellInv cellAlpha) ih
  whiskerLeftCongr {_ _ _ oneCell _ _ _ _} ih :=
    SaturatedConvOver.castBoundaryCongr _ _ (SaturatedConvOver.whiskerLeftCongr (reseatPathInv oneCell) ih)
  whiskerRightCongr {_ _ _ _ _ oneCell _ _} ih :=
    SaturatedConvOver.castBoundaryCongr _ _ (SaturatedConvOver.whiskerRightCongr (reseatPathInv oneCell) ih)
  refl cell := SaturatedConvOver.refl (reseatCellInv cell)
  symm ih := SaturatedConvOver.symm ih
  trans ihLeft ihRight := SaturatedConvOver.trans ihLeft ihRight

/-- ★★ **The BACKWARD reseat conv transport** — a bespoke saturated convertibility transports along `reseatCellInv`
to the reconstructed image: `SaturatedConvOver monadModeSignature MonadLawRel a b ==> SaturatedConvOver
monadComputad.toModeSignature MonadLawRelReconstructed (reseatCellInv a) (reseatCellInv b)`.  Via the universal
property `SaturatedConvOver.recInto` with `reseatCongruenceBackward`.  The isTrue-leg direction of the reseated
reconstructed decider. -/
theorem reseatConvBackward {sourceMode targetMode : monadModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver monadModeSignature MonadLawRel cellAlpha cellBeta) :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
      (reseatCellInv cellAlpha) (reseatCellInv cellBeta) :=
  SaturatedConvOver.recInto reseatCongruenceBackward conv

/-! ## B5 — the reseated reconstructed-signature decider + both verdicts on real recon cells

The decider over `monadComputad.toModeSignature` `MonadLawRelReconstructed` runs the shipped bespoke
`monadSaturatedTwoCellDecision` on the `reseatCell`-images, bridged by `monadSaturated_iff_generic`.  The isFalse
leg is LIVE and roundtrip-free (`monadReconRefutes`, the shipped forward transport).  The isTrue leg needs the
REFLECTION `SaturatedConvOver monadModeSignature MonadLawRel (reseatCell a) (reseatCell b) ==> SaturatedConvOver
monadComputad.toModeSignature MonadLawRelReconstructed a b` — which is exactly `reseatConvBackward` (B4) COMPOSED
with the cell round-trip `reseatCellInv (reseatCell a) = a`.  The general decider is therefore stated CONDITIONAL
on that reflection; the round-trip is the honest residual (see the marker). -/

/-- The reconstructed monad face δ₁ — the reconstructed unit whiskered on the RIGHT by `t`: a 2-cell `t ⇒ t·t`. -/
def reconFaceDeltaOne :
    RawTwoCellExpr monadComputad.toModeSignature
      monadComputadReconstructedT monadComputadReconstructedTT :=
  RawTwoCellExpr.whiskerRight (signature := monadComputad.toModeSignature) monadComputadReconstructedT reconEta

/-- The reconstructed monad face δ₀ — the reconstructed unit whiskered on the LEFT by `t`: a 2-cell `t ⇒ t·t`
(the domain `t·id` is DEFINITIONALLY `t`).  The δ₀/δ₁ counterpart of `reconFaceDeltaOne`. -/
def reconFaceDeltaZero :
    RawTwoCellExpr monadComputad.toModeSignature
      monadComputadReconstructedT monadComputadReconstructedTT :=
  RawTwoCellExpr.whiskerLeft (signature := monadComputad.toModeSignature) monadComputadReconstructedT reconEta

/-- `reseatCell` of the reconstructed δ₁ face IS the bespoke δ₁ face `whiskerRight monadT monadUnitTwoCell` (the
`reseatPath_composePath` cast on `t`-powers collapses definitionally, then the `eta` generator inversion). -/
theorem reseatCell_reconFaceDeltaOne :
    reseatCell reconFaceDeltaOne
      = RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell :=
  congrArg (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT) reseatCell_reconEta

/-- `reseatCell` of the reconstructed δ₀ face IS the bespoke δ₀ face `whiskerLeft monadT monadUnitTwoCell`. -/
theorem reseatCell_reconFaceDeltaZero :
    reseatCell reconFaceDeltaZero
      = RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell :=
  congrArg (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT) reseatCell_reconEta

/-- ★★ **The isFalse verdict on a REAL reconstructed pair (LIVE, roundtrip-free)** — the two reconstructed monad
faces `reconFaceDeltaOne` (δ₁, monotone map `[1]`) and `reconFaceDeltaZero` (δ₀, monotone map `[0]`) are NOT
convertible over the reconstructed signature.  Discharged by the shipped forward transport `monadReconRefutes`:
their `reseatCell`-images are the bespoke faces (`reseatCell_reconFaceDeltaOne` / `Zero`), which the shipped
walking-monad decision SEPARATES (`monadDecision_no_faces`, via `monadSaturated_iff_generic`).  The reseated
decider's isFalse branch made literal on a concrete separating pair. -/
theorem reconFacesDecideFalse :
    ¬ SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
        reconFaceDeltaOne reconFaceDeltaZero :=
  monadReconRefutes (fun conv =>
    monadDecision_no_faces
      ((monadSaturated_iff_generic _ _).mpr
        (reseatCell_reconFaceDeltaOne ▸ reseatCell_reconFaceDeltaZero ▸ conv)))

/-- ★★ **The isTrue verdict on a REAL reconstructed pair (LIVE), EXERCISING the backward transport** — the two
reconstructed associativity foldings `t·t·t ⇒ t` (`reseatCellInv monadAssocLeftCell` / `reseatCellInv
monadAssocRightCell`, DEFINITIONALLY the reconstructed `mu . (mu |> t)` / `mu . (t <| mu)`) ARE saturated
convertible over the reconstructed signature.  Discharged by `reseatConvBackward` (B4) on the shipped bespoke
associativity decision `monadDecision_yes_assoc` (both fold to the width-3 degeneracy `[0,0,0]`).  The reseated
decider's isTrue branch made literal on a concrete convertible pair, routed through the inverse functor. -/
theorem reconAssocDecidesTrue :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
      (reseatCellInv monadAssocLeftCell) (reseatCellInv monadAssocRightCell) :=
  reseatConvBackward ((monadSaturated_iff_generic _ _).mp monadDecision_yes_assoc)

/-- ★ The reconstructed left-unit law holds directly as a reconstructed saturated-conv row — the trivial isTrue
verdict on the reconstructed left-unit composite. -/
theorem reconLeftUnitDecidesTrue :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed reconLeftUnitCell reconIdTCell :=
  SaturatedConvOver.ofRelation MonadLawRelReconstructed.leftUnit

/-- ★★ **The reseated reconstructed-signature decider, CONDITIONAL on the reflection.**  A total
`DecidableSaturatedConvForRel monadComputad.toModeSignature MonadLawRelReconstructed` obtained by running the
shipped bespoke `monadSaturatedTwoCellDecision` on the `reseatCell`-images.  The isFalse leg ships UNCONDITIONALLY
(`monadReconRefutes` + `monadSaturated_iff_generic`); the isTrue leg is supplied by the `reflect` hypothesis — the
reconstructed-signature reflection of a bespoke convertibility.  `reflect` is inhabited by `reseatConvBackward`
(B4) COMPOSED with the cell round-trip `reseatCellInv (reseatCell a) = a`; the round-trip is the sole residual for
the UNCONDITIONAL decider (see `fxAmalgInverse_hasReseatedReconstructionDecider`). -/
def monadReconstructedDecisionViaReflection
    (reflect : {sourceMode targetMode : Fin 1} →
      {sourcePath targetPath : ModalityPath monadComputad.toModeGraph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath} →
      SaturatedConvOver monadModeSignature MonadLawRel (reseatCell cellAlpha) (reseatCell cellBeta) →
      SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed cellAlpha cellBeta) :
    DecidableSaturatedConvForRel monadComputad.toModeSignature MonadLawRelReconstructed :=
  fun cellAlpha cellBeta =>
    match monadSaturatedTwoCellDecision (reseatCell cellAlpha) (reseatCell cellBeta) with
    | isTrue hbespoke => isTrue (reflect ((monadSaturated_iff_generic _ _).mp hbespoke))
    | isFalse hbespoke =>
        isFalse (monadReconRefutes (fun hgen => hbespoke ((monadSaturated_iff_generic _ _).mpr hgen)))

/-! ## B6 — the round-trip nodes: the PATH leg `reseatPathInv (reseatPath path) = path`

The reseated decider `monadReconstructedDecisionViaReflection` (B5) is CONDITIONAL on the reflection, which is
`reseatConvBackward` (B4) COMPOSED with the CELL round-trip `reseatCellInv (reseatCell cell) = cell`.  The cell
round-trip factors through the PATH round-trip `reseatPathInv (reseatPath path) = path` (this section) and the GEN
round-trip (below).  The path leg reconstructs a reconstructed `t`-power from its length: the wall the r1 marker
named is that `path` lives over the FIXED `Fin 1` endpoints `⟨0⟩ ⟨0⟩` (non-variable inductive-family indices), so
structural recursion on `path` is unavailable — the `cons` case must pin the (free) middle mode to `⟨0⟩`, which
`subst` cannot do inside a structural recursion on `path`.  The fix (the standard fixed-index generalization): the
recursion is on the LENGTH `fuel` (a `Nat`, structurally decreasing), with `path` carried as data and the middle
mode pinned per step.  All `Eq.rec` / no `HEq`, STRUCTURAL, propext-free. -/

/-- **Middle-mode pin** — a reconstructed 1-generator at source `⟨0⟩` forces its target mode to `⟨0⟩` (the sole
`Fin 1` inhabitant), read off the stored endpoint witness by `Prod.snd` congruence.  Propext-free (subtype +
`Fin`-value decomposition, NOT `Fin.cases`). -/
theorem reconModalityTargetZero {middleMode : Fin 1}
    (modality : monadComputad.Modality (⟨0, by decide⟩ : Fin 1) middleMode) :
    middleMode = (⟨0, by decide⟩ : Fin 1) :=
  match modality with
  | ⟨⟨0, _⟩, hproof⟩ => (congrArg Prod.snd hproof).symm
  | ⟨⟨_ + 1, isLt⟩, _⟩ => False.elim (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ isLt))

/-- **Generator uniqueness at `⟨0⟩ ⟨0⟩`** — the reconstructed 1-cell family `Modality ⟨0⟩ ⟨0⟩` is a subsingleton
(one index `⟨0⟩`, proof-irrelevant property), so every inhabitant IS the canonical `⟨⟨0⟩, rfl⟩`.  Propext-free. -/
theorem reconModalityUnique
    (modality : monadComputad.Modality (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1)) :
    modality = ⟨⟨0, by decide⟩, rfl⟩ :=
  match modality with
  | ⟨⟨0, _⟩, _⟩ => rfl
  | ⟨⟨_ + 1, isLt⟩, _⟩ => False.elim (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ isLt))

/-- **The PATH round-trip, fuelled by length** — `reseatPathInv (reseatPath path) = path` for a reconstructed
`t`-power over the FIXED `⟨0⟩ ⟨0⟩` endpoints.  Structural recursion on the `Nat` fuel (the length), so the middle
mode `subst` in the `cons` case never disturbs the recursion measure (the fixed-index generalization the r1
marker's wall requires).  Every arm `Eq.rec` / propext-free. -/
theorem reseatPathInv_reseatPath_fueled :
    (fuel : Nat) →
    (path : ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1)) →
    path.length = fuel →
    reseatPathInv (reseatPath path) = path
  | 0, ModalityPath.nil _, _ => rfl
  | 0, ModalityPath.cons _ _, hlen => Nat.noConfusion hlen
  | _ + 1, ModalityPath.nil _, hlen => Nat.noConfusion hlen
  | fuel + 1, ModalityPath.cons modality rest, hlen => by
      have hmiddle := reconModalityTargetZero modality
      subst hmiddle
      have hrest : rest.length = fuel := Nat.succ.inj hlen
      have ih := reseatPathInv_reseatPath_fueled fuel rest hrest
      show ModalityPath.cons
            (⟨⟨0, by decide⟩, rfl⟩ :
              monadComputad.Modality (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1))
            (reseatPathInv (reseatPath rest)) = ModalityPath.cons modality rest
      rw [ih, reconModalityUnique modality]

/-- ★★ **The PATH round-trip** — `reseatPathInv (reseatPath path) = path` on the mono-mode fibre.  The inverse
1-cell functor is a genuine section of the forward 1-cell functor on the reconstructed `t`-powers; instantiates
the length-fuelled recursion at the actual length.  First of the two round-trip nodes the r1 marker walled. -/
theorem reseatPathInv_reseatPath
    (path : ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1)) :
    reseatPathInv (reseatPath path) = path :=
  reseatPathInv_reseatPath_fueled path.length path rfl

/-! ## B7 — the GEN leg: `reseatGenInv (reseatGen g) = g` (modulo boundary cast)

The GEN round-trip is the r1 marker's "hard node": for a GENERIC reconstructed generator `g`, the forward
`reseatGen g` is a STUCK `castMonadTwoCell` (the boundary is only PROPOSITIONALLY `(nil point, monadT)` via the
interpreter witnesses), so `reseatGenInv (reseatGen g)` does not reduce through the matcher.  The unstick is a
NEW naturality lemma (`reseatGenInv_castMonadTwoCell` / `_val`): `reseatGenInv` commutes with the boundary cast
(`cases` the two equalities then `rfl`).  With it, the index of the round-trip is READ OFF: since `reseatGen`
sends a reconstructed generator of index `i` to the bespoke generator (`eta` at `0`, `mu` at `1`) and `reseatGenInv`
sends `eta` / `mu` back to the reconstructed generators of index `0` / `1`, the composite PRESERVES the index —
`(reseatGenInv (reseatGen g)).val = g.val` (a homogeneous `Fin 2` equality, no transport).  `Eq.rec`, no `HEq`. -/

/-- **The reconstructed-side naturality of the inverse generator map through the boundary cast** —
`reseatGenInv (castMonadTwoCell hfirst hsecond cell)` is the `reseatPathInv`-image cast of `reseatGenInv cell`.
`cases` the two boundary equalities (`castMonadTwoCell rfl rfl` collapses), then `rfl`.  The recon-side mirror of
`castMonadTwoCell`; the tool that unsticks the forward `reseatGen`'s stuck cast in the round-trip. -/
theorem reseatGenInv_castMonadTwoCell
    {firstPath firstPath' secondPath secondPath' :
      ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hfirst : firstPath = firstPath') (hsecond : secondPath = secondPath')
    (cell : MonadTwoCell firstPath secondPath) :
    reseatGenInv (castMonadTwoCell hfirst hsecond cell)
      = (congrArg reseatPathInv hfirst) ▸ (congrArg reseatPathInv hsecond) ▸ reseatGenInv cell := by
  cases hfirst; cases hsecond; rfl

/-- **Naturality at the INDEX level** — the `Fin 2` index of `reseatGenInv` is invariant under the boundary cast
(the transports on the reconstructed-generator subtype leave its `Fin 2` index untouched).  A homogeneous `Fin 2`
equality, no transport in the statement; `cases` the two equalities then `rfl`.  This is the form the round-trip's
index read-off consumes. -/
theorem reseatGenInv_castMonadTwoCell_val
    {firstPath firstPath' secondPath secondPath' :
      ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hfirst : firstPath = firstPath') (hsecond : secondPath = secondPath')
    (cell : MonadTwoCell firstPath secondPath) :
    (reseatGenInv (castMonadTwoCell hfirst hsecond cell)).val = (reseatGenInv cell).val := by
  cases hfirst; cases hsecond; rfl

/-- ★★ **The GEN round-trip, index level** — `(reseatGenInv (reseatGen g)).val = g.val`: the inverse generator map
after the forward one PRESERVES the reconstructed 2-generator index.  The r1 marker's hard node, discharged: the
modes are pinned to `⟨0⟩` (the sole `Fin 1` inhabitant) so `reseatGen` reduces to a `castMonadTwoCell` of `eta`
(index `0`) / `mu` (index `1`); the naturality lemma reads the index off through the otherwise-stuck cast.  The
statement is a homogeneous `Fin 2` equality (`.val` is boundary-independent), so no `HEq`; the full boundary-cast
equation follows by `Subtype.ext`. -/
theorem reseatGenInvReseatGen_val : {sourceMode targetMode : Fin 1} →
    {sourcePath targetPath : ModalityPath monadComputad.toModeGraph sourceMode targetMode} →
    (g : monadComputad.ReconstructedTwoCell sourcePath targetPath) →
    (reseatGenInv (reseatGen g)).val = g.val
  | ⟨0, _⟩, ⟨0, _⟩, _, _, ⟨⟨0, _⟩, hlhs, hrhs⟩ =>
      reseatGenInv_castMonadTwoCell_val
        (Option.some.inj (congrArg reseatInterp hlhs))
        (Option.some.inj (congrArg reseatInterp hrhs)) MonadTwoCell.eta
  | ⟨0, _⟩, ⟨0, _⟩, _, _, ⟨⟨1, _⟩, hlhs, hrhs⟩ =>
      reseatGenInv_castMonadTwoCell_val
        (Option.some.inj (congrArg reseatInterp hlhs))
        (Option.some.inj (congrArg reseatInterp hrhs)) MonadTwoCell.mu
  | ⟨0, _⟩, ⟨0, _⟩, _, _, ⟨⟨_ + 2, isLt⟩, _⟩ =>
      absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt)) (Nat.not_lt_zero _)
  | ⟨_ + 1, isLt⟩, _, _, _, _ =>
      absurd (Nat.lt_of_succ_lt_succ isLt) (Nat.not_lt_zero _)
  | ⟨0, _⟩, ⟨_ + 1, isLt⟩, _, _, _ =>
      absurd (Nat.lt_of_succ_lt_succ isLt) (Nat.not_lt_zero _)

/-- Transporting a reconstructed generator across boundary-path equalities leaves its `Fin 2` index untouched
(the index type is boundary-independent).  `cases` both equalities then `rfl`. -/
theorem reconTwoCell_doubleTransport_val {sourceMode targetMode : Fin 1}
    {sourcePath sourcePath' targetPath targetPath' :
      ModalityPath monadComputad.toModeGraph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (g : monadComputad.ReconstructedTwoCell sourcePath targetPath) :
    (hsource ▸ htarget ▸ g).val = g.val := by
  cases hsource; cases htarget; rfl

/-- ★★ **The GEN round-trip (full)** — `reseatGenInv (reseatGen g)` is the boundary-cast of `g` back onto the
`reseatPathInv (reseatPath ..)` image boundary.  The r1 marker's hard node, CLOSED: since the round-trip preserves
the `Fin 2` index (`reseatGenInvReseatGen_val`) and both sides are proof-irrelevant subtypes at the SAME boundary,
`Subtype.ext` upgrades the index equality to the full generator equality (the transport on the RHS leaves the
index fixed by `reconTwoCell_doubleTransport_val`).  All `Eq.rec` / no `HEq`. -/
theorem reseatGenInv_reseatGen
    {sourcePath targetPath : ModalityPath monadComputad.toModeGraph
      (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1)}
    (g : monadComputad.ReconstructedTwoCell sourcePath targetPath) :
    reseatGenInv (reseatGen g)
      = ((reseatPathInv_reseatPath sourcePath).symm ▸
          (reseatPathInv_reseatPath targetPath).symm ▸ g
          : monadComputad.ReconstructedTwoCell (reseatPathInv (reseatPath sourcePath))
              (reseatPathInv (reseatPath targetPath))) :=
  Subtype.ext (by
    rw [reconTwoCell_doubleTransport_val]
    exact reseatGenInvReseatGen_val g)

/-- **Stripping a shared boundary cast off a saturated convertibility** — the inverse of
`SaturatedConvOver.castBoundaryCongr`.  Fully generic (`sourcePath'` / `targetPath'` are FRESH variables, so
`cases` on the boundary equalities is unobstructed — unlike at the round-trip call site, where the cast target is
`reseatPathInv (reseatPath ..)`, occurs-blocked).  The tool that discharges the reflection after the cell
round-trip rewrites both sides onto a shared cast. -/
theorem saturatedConvOver_castBoundaryStrip {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (conv : SaturatedConvOver signature baseRel
      (RawTwoCellExpr.castBoundary hsource htarget cellAlpha)
      (RawTwoCellExpr.castBoundary hsource htarget cellBeta)) :
    SaturatedConvOver signature baseRel cellAlpha cellBeta := by
  cases hsource; cases htarget; exact conv

/-! ## Honesty markers -/

/-- ★★ **Honesty marker (`true`) — the INVERSE reseat functor + the BACKWARD conv transport SHIP (MODE-ADMIT-INV
r1).**  The FIXED-pair `(monadModeSignature, monadComputad.toModeSignature)` inverse half is BUILT zero-axiom: the
inverse 1-cell functor `reseatPathInv` (bespoke `t`-powers to reconstructed, `reseatPathInv_monadT` /
`reseatPathInv_monadTThenT` by `rfl`) with its homomorphism law `reseatPathInv_composePath` and the length
length faithfulness `reseatPathInv_length`; the DIRECT inverse generator map `reseatGenInv` (bespoke `eta`/`mu` to the
reconstructed generators, cast-free — the reconstructed boundaries are the `reseatPathInv` images DEFINITIONALLY);
the inverse free 2-cell functor `reseatCellInv` (+ its per-constructor reduction lemmas); the thirteen-constructor
`TwoCellConvFull` functoriality `reseatCellInv_preservesConv` (the exact inverse mirror of
`reseatCell_preservesConv`); the three backward law rows (`reconLeftUnitConvBackward` etc.); and the BACKWARD conv
transport `reseatConvBackward` (`recInto` into the `reseatCellInv`-image congruence).  fib-3-DECOUPLED (no 2-cell
equality modulo the 3-cell laws is decided), all `Eq.rec` / no `HEq`.  `= true`. -/
def fxAmalgInverse_hasBackwardReseatTransport : Bool := true

/-- ★★ **Honesty marker (`true`) — the reseated reconstructed-signature decider ASSEMBLES, with both verdicts LIVE
on real recon cells.**  `monadReconstructedDecisionViaReflection` is a total `DecidableSaturatedConvForRel` over
`monadComputad.toModeSignature MonadLawRelReconstructed` whose isFalse leg ships UNCONDITIONALLY (`monadReconRefutes`
+ `monadSaturated_iff_generic`) and whose isTrue leg is the reconstructed-signature reflection.  Both verdicts are
demonstrated LIVE on concrete real reconstructed cells: isFalse on the two separating monad faces
(`reconFacesDecideFalse`, δ₁ vs δ₀, roundtrip-free via the forward transport) and isTrue on the two associativity
foldings (`reconAssocDecidesTrue`, routed through the backward transport `reseatConvBackward`).  `= true`. -/
def fxAmalgInverse_hasReseatedDeciderBothVerdicts : Bool := true

/-- ★★ **Honesty marker (`true`, MODE-ADMIT-INV r2) — BOTH round-trip nodes are DISCHARGED, zero-axiom.**  The r1
marker named the round-trip as a "genuine WALL on TWO nodes"; r2 CLOSES both, downgrading the wall to bounded cast
labor:

  * **PATH leg** `reseatPathInv (reseatPath path) = path` (`reseatPathInv_reseatPath`) — the FIXED-index obstruction
    (`path` over `⟨0⟩ ⟨0⟩`, structural recursion unavailable) is dissolved by the standard fixed-index
    generalization: recurse on the LENGTH `fuel` (`reseatPathInv_reseatPath_fueled`), pinning the `cons` middle mode
    with `reconModalityTargetZero` / `reconModalityUnique` so the `subst` never disturbs the `Nat`-fuel measure.
  * **GEN leg** `reseatGenInv (reseatGen g) = g` (`reseatGenInv_reseatGen`) — the STUCK `castMonadTwoCell` is
    unstuck by the recon-side naturality `reseatGenInv_castMonadTwoCell` / `_val` (`cases` the two boundary
    equalities), which READS the reconstructed 2-generator index off through the otherwise-stuck cast:
    `reseatGenInvReseatGen_val` shows the round-trip PRESERVES the `Fin 2` index (a homogeneous equality, no `HEq`),
    and `Subtype.ext` (proof-irrelevant subtype) upgrades it to the full boundary-cast equation.

Both nodes are `Eq.rec` / no `HEq`, STRUCTURAL, per-declaration `#assert_no_axioms`-gated.  `= true`. -/
def fxAmalgInverse_hasRoundTripNodesDischarged : Bool := true

/-- ★ **Honesty marker (`false`) — the UNCONDITIONAL two-sided reseated decider still needs the cell round-trip
ASSEMBLY (no longer a wall — bounded cast labor over the two discharged nodes).**  `fxAmalg_hasReconstructionDecoderReseat`
(`DeciderReseat.lean`) named the residual for the FULL two-sided decider: after the FORWARD transport (r4, isFalse
leg literal) the isTrue leg needs the inverse functor + the round-trip.  r1 shipped the inverse functor and the
BACKWARD conv transport (`reseatConvBackward`) and assembled the decider CONDITIONAL on the reflection
(`monadReconstructedDecisionViaReflection`).  r2 DISCHARGES both round-trip NODES
(`fxAmalgInverse_hasRoundTripNodesDischarged`: `reseatPathInv_reseatPath`, `reseatGenInv_reseatGen`) plus the
saturated-conv cast-strip tool (`saturatedConvOver_castBoundaryStrip`).

What remains to FLIP this marker (and inhabit `reflect` unconditionally) is the CELL round-trip
`reseatCellInv (reseatCell cell) = castBoundary .. cell` — the structural functoriality assembling the two node
results over the whole `RawTwoCellExpr` grammar (`gen` via `reseatGenInv_reseatGen`, `id` via `castBoundaryId`,
the whisker cases reconciling `reseatCell`'s forward `reseatPath_composePath` cast with `reseatCellInv`'s
`reseatPathInv_composePath` cast through the `ReseatCastKit` algebra) — followed by `reseatConvBackward` +
`saturatedConvOver_castBoundaryStrip` to inhabit `reflect`, then `monadReconstructedDecisionViaReflection` applied
to it.  This is bounded, all-`Eq.rec` cast-assembly LABOR over generic `Fin 1` endpoints (mode-pinned as in the
nodes), NOT a mathematical wall.  Both decider verdicts remain LIVE on real recon cells (isFalse roundtrip-free,
isTrue via the backward transport), so completeness is DEMONSTRATED on concrete pairs; only the GENERAL
unconditional isTrue leg awaits the cell-round-trip assembly.  `= false` (unconditional flip of
`fxAmalg_hasReconstructionDecoderReseat` remains the residual). -/
def fxAmalgInverse_hasReseatedReconstructionDecider : Bool := false

end FX1Poly.Polygraph.Amalgam
