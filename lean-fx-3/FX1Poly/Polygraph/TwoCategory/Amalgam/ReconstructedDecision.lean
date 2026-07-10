import FX1Poly.Polygraph.TwoCategory.Amalgam.MonadReseatInverse

/-! # Polygraph/TwoCategory/Amalgam/ReconstructedDecision — the CELL round-trip, the reconstructed-signature
REFLECTION, and the UNCONDITIONAL reseated decider (MODE-ADMIT-INV-N3)

`MonadReseatInverse.lean` (MODE-ADMIT-INV r1/r2) shipped the INVERSE reseat functor `reseatCellInv`, the BACKWARD
conv transport `reseatConvBackward`, the reflection-CONDITIONAL decider `monadReconstructedDecisionViaReflection`,
and both round-trip NODES (`reseatPathInv_reseatPath`, `reseatGenInv_reseatGen`) plus the cast-strip tool
`saturatedConvOver_castBoundaryStrip`.  Its r2 marker `fxAmalgInverse_hasReseatedReconstructionDecider = false`
named the sole residual for the UNCONDITIONAL decider: the CELL round-trip assembling the two nodes over the whole
`RawTwoCellExpr` grammar.

This file discharges that residual and ships the unconditional decider:

  * **`reseatCellInv_reseatCell`** (B1) — the CELL round-trip `reseatCellInv (reseatCell cell) = castBoundary .. cell`
    over the fixed `⟨0⟩ ⟨0⟩` endpoints, by structural cell-size fuel (`reseatCellInvReseatCellFueled`) with the
    middle-mode pins in the two whisker steps.  All `Eq.rec` / no `HEq`, STRUCTURAL.
  * **`reseatReflect`** (B2) — the reconstructed-signature reflection, inhabiting the `reflect` hypothesis
    UNCONDITIONALLY (backward transport ∘ cell round-trip ∘ cast-strip).
  * **`monadReconstructedDecision`** (B3) — the UNCONDITIONAL `DecidableSaturatedConvForRel
    monadComputad.toModeSignature MonadLawRelReconstructed`, both verdicts LIVE on real reconstructed cells.

RETIREMENT-ENABLER: this is the unconditional-decider milestone, NOT island dissolution — the decider still
transitively imports `WalkingMonad/MonadWordProblem`, and the `SaturatedOver`/`monadRelationFamily` root pins are
untouched, so honest deletion count this round is ZERO (see `fxRecon_hasUnconditionalReconstructionDecider`).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-- Every free 2-cell has structural size at least one (signature-generic). -/
theorem oneLeRawCellSize {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : 1 ≤ cell.size :=
  match cell with
  | .gen _ => Nat.le_refl 1
  | .id _ => Nat.le_refl 1
  | .vcomp cellL cellR => Nat.le_add_left 1 (cellL.size + cellR.size)
  | .whiskerLeft _ body => Nat.le_add_left 1 body.size
  | .whiskerRight _ body => Nat.le_add_left 1 body.size

/-- A `gen` of a boundary-transported generator IS the boundary cast of the `gen` (fresh targets so `cases`). -/
theorem genTransportCast {sourceMode targetMode : Fin 1}
    {sourcePath sourcePath' targetPath targetPath' :
      ModalityPath monadComputad.toModeGraph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (g : monadComputad.ReconstructedTwoCell sourcePath targetPath) :
    RawTwoCellExpr.gen (signature := monadComputad.toModeSignature)
        (hsource ▸ htarget ▸ g : monadComputad.ReconstructedTwoCell sourcePath' targetPath')
      = RawTwoCellExpr.castBoundary hsource htarget
          (RawTwoCellExpr.gen (signature := monadComputad.toModeSignature) g) := by
  cases hsource; cases htarget; rfl

/-- Cancelling a boundary cast against its symm (fresh targets so `cases`). -/
theorem castBoundarySymmCancel {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellHigh : RawTwoCellExpr signature sourcePath' targetPath'}
    {cellLow : RawTwoCellExpr signature sourcePath targetPath}
    (heq : cellHigh = RawTwoCellExpr.castBoundary hsource htarget cellLow) :
    RawTwoCellExpr.castBoundary hsource.symm htarget.symm cellHigh = cellLow := by
  cases hsource; cases htarget; exact heq

/-- The whiskerLeft reconciliation step of the cell round-trip. -/
theorem reseatCellInvReseatCellWhiskerLeftStep
    (oc : ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1))
    {oneCellG oneCellH : ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1)}
    (body : RawTwoCellExpr monadComputad.toModeSignature oneCellG oneCellH)
    (ihBody : reseatCellInv (reseatCell body)
        = RawTwoCellExpr.castBoundary (reseatPathInv_reseatPath oneCellG).symm
            (reseatPathInv_reseatPath oneCellH).symm body) :
    reseatCellInv (reseatCell (RawTwoCellExpr.whiskerLeft oc body))
      = RawTwoCellExpr.castBoundary
          (reseatPathInv_reseatPath (composePath oc oneCellG)).symm
          (reseatPathInv_reseatPath (composePath oc oneCellH)).symm
          (RawTwoCellExpr.whiskerLeft oc body) := by
  have hWhiskerPath :
      RawTwoCellExpr.whiskerLeft (reseatPathInv (reseatPath oc)) body
        = RawTwoCellExpr.castBoundary
            (congrArg (fun path => composePath path oneCellG) (reseatPathInv_reseatPath oc)).symm
            (congrArg (fun path => composePath path oneCellH) (reseatPathInv_reseatPath oc)).symm
            (RawTwoCellExpr.whiskerLeft oc body) :=
    (castBoundarySymmCancel _ _
      (ReseatCastKit.whiskerLeftPathCongr (reseatPathInv_reseatPath oc) body)).symm
  show reseatCellInv (RawTwoCellExpr.castBoundary (reseatPath_composePath oc oneCellG).symm
        (reseatPath_composePath oc oneCellH).symm
        (RawTwoCellExpr.whiskerLeft (reseatPath oc) (reseatCell body)))
      = RawTwoCellExpr.castBoundary (reseatPathInv_reseatPath (composePath oc oneCellG)).symm
          (reseatPathInv_reseatPath (composePath oc oneCellH)).symm (RawTwoCellExpr.whiskerLeft oc body)
  exact
    (reseatCellInv_castBoundary _ _ _).trans
      ((congrArg (RawTwoCellExpr.castBoundary _ _)
          ((reseatCellInv_whiskerLeft (reseatPath oc) (reseatCell body)).trans
            ((congrArg (RawTwoCellExpr.castBoundary _ _)
                (((congrArg (RawTwoCellExpr.whiskerLeft (reseatPathInv (reseatPath oc))) ihBody).trans
                    (ReseatCastKit.whiskerLeftCastBoundary (reseatPathInv (reseatPath oc)) _ _ body)).trans
                  ((congrArg (RawTwoCellExpr.castBoundary _ _) hWhiskerPath).trans
                    (ReseatCastKit.castBoundaryTrans _ _ _ _ _)))).trans
              (ReseatCastKit.castBoundaryTrans _ _ _ _ _)))).trans
        (ReseatCastKit.castBoundaryTrans _ _ _ _ _))

/-- The whiskerRight reconciliation step of the cell round-trip. -/
theorem reseatCellInvReseatCellWhiskerRightStep
    (oc : ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1))
    {oneCellF oneCellG : ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1)}
    (body : RawTwoCellExpr monadComputad.toModeSignature oneCellF oneCellG)
    (ihBody : reseatCellInv (reseatCell body)
        = RawTwoCellExpr.castBoundary (reseatPathInv_reseatPath oneCellF).symm
            (reseatPathInv_reseatPath oneCellG).symm body) :
    reseatCellInv (reseatCell (RawTwoCellExpr.whiskerRight oc body))
      = RawTwoCellExpr.castBoundary
          (reseatPathInv_reseatPath (composePath oneCellF oc)).symm
          (reseatPathInv_reseatPath (composePath oneCellG oc)).symm
          (RawTwoCellExpr.whiskerRight oc body) := by
  have hWhiskerPath :
      RawTwoCellExpr.whiskerRight (reseatPathInv (reseatPath oc)) body
        = RawTwoCellExpr.castBoundary
            (congrArg (composePath oneCellF) (reseatPathInv_reseatPath oc)).symm
            (congrArg (composePath oneCellG) (reseatPathInv_reseatPath oc)).symm
            (RawTwoCellExpr.whiskerRight oc body) :=
    (castBoundarySymmCancel _ _
      (ReseatCastKit.whiskerRightPathCongr (reseatPathInv_reseatPath oc) body)).symm
  show reseatCellInv (RawTwoCellExpr.castBoundary (reseatPath_composePath oneCellF oc).symm
        (reseatPath_composePath oneCellG oc).symm
        (RawTwoCellExpr.whiskerRight (reseatPath oc) (reseatCell body)))
      = RawTwoCellExpr.castBoundary (reseatPathInv_reseatPath (composePath oneCellF oc)).symm
          (reseatPathInv_reseatPath (composePath oneCellG oc)).symm (RawTwoCellExpr.whiskerRight oc body)
  exact
    (reseatCellInv_castBoundary _ _ _).trans
      ((congrArg (RawTwoCellExpr.castBoundary _ _)
          ((reseatCellInv_whiskerRight (reseatPath oc) (reseatCell body)).trans
            ((congrArg (RawTwoCellExpr.castBoundary _ _)
                (((congrArg (RawTwoCellExpr.whiskerRight (reseatPathInv (reseatPath oc))) ihBody).trans
                    (ReseatCastKit.whiskerRightCastBoundary (reseatPathInv (reseatPath oc)) _ _ body)).trans
                  ((congrArg (RawTwoCellExpr.castBoundary _ _) hWhiskerPath).trans
                    (ReseatCastKit.castBoundaryTrans _ _ _ _ _)))).trans
              (ReseatCastKit.castBoundaryTrans _ _ _ _ _)))).trans
        (ReseatCastKit.castBoundaryTrans _ _ _ _ _))

/-- The cell round-trip, fuelled by structural cell size (the middle-mode pins live in the whisker cases). -/
theorem reseatCellInvReseatCellFueled : (fuel : Nat) →
    {sourcePath targetPath :
      ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1)} →
    (cell : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath) →
    cell.size ≤ fuel →
    reseatCellInv (reseatCell cell)
      = RawTwoCellExpr.castBoundary (reseatPathInv_reseatPath sourcePath).symm
          (reseatPathInv_reseatPath targetPath).symm cell := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourcePath targetPath cell hfuel
      exact absurd (Nat.le_trans (oneLeRawCellSize cell) hfuel) (Nat.not_succ_le_zero 0)
  | succ fuel ih =>
      intro sourcePath targetPath cell hfuel
      match cell, hfuel with
      | .gen g, _ =>
          exact (congrArg RawTwoCellExpr.gen (reseatGenInv_reseatGen g)).trans
            (genTransportCast (reseatPathInv_reseatPath sourcePath).symm
              (reseatPathInv_reseatPath targetPath).symm g)
      | .id path, _ =>
          exact (ReseatCastKit.castBoundaryId (reseatPathInv_reseatPath path).symm).symm
      | @RawTwoCellExpr.vcomp _ _ _ oneCellF oneCellG oneCellH cellL cellR, hf =>
          exact
            ((congrArg (fun leftCell => RawTwoCellExpr.vcomp leftCell (reseatCellInv (reseatCell cellR)))
                  (ih cellL (Nat.le_trans (Nat.le_add_right cellL.size cellR.size)
                    (Nat.le_of_succ_le_succ hf)))).trans
              (congrArg (RawTwoCellExpr.vcomp (RawTwoCellExpr.castBoundary
                    (reseatPathInv_reseatPath oneCellF).symm (reseatPathInv_reseatPath oneCellG).symm cellL))
                (ih cellR (Nat.le_trans (Nat.le_add_left cellR.size cellL.size)
                  (Nat.le_of_succ_le_succ hf))))).trans
            (ReseatCastKit.castBoundaryVcomp (reseatPathInv_reseatPath oneCellF).symm
              (reseatPathInv_reseatPath oneCellG).symm (reseatPathInv_reseatPath oneCellH).symm cellL cellR).symm
      | @RawTwoCellExpr.whiskerLeft _ _ mm _ oc oneCellG oneCellH body, hf =>
          have hmm : mm = (⟨0, by decide⟩ : Fin 1) := (finOneEqZero mm).symm
          subst hmm
          exact reseatCellInvReseatCellWhiskerLeftStep oc body
            (ih body (Nat.le_of_succ_le_succ hf))
      | @RawTwoCellExpr.whiskerRight _ _ mm _ oneCellF oneCellG oc body, hf =>
          have hmm : mm = (⟨0, by decide⟩ : Fin 1) := (finOneEqZero mm).symm
          subst hmm
          exact reseatCellInvReseatCellWhiskerRightStep oc body
            (ih body (Nat.le_of_succ_le_succ hf))

/-- ★★ **The CELL round-trip** — `reseatCellInv (reseatCell cell)` is the boundary cast of `cell` back onto the
`reseatPathInv (reseatPath ..)` image boundary, for a reconstructed cell over the fixed `⟨0⟩ ⟨0⟩` endpoints. -/
theorem reseatCellInv_reseatCell
    {sourcePath targetPath :
      ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1)}
    (cell : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath) :
    reseatCellInv (reseatCell cell)
      = RawTwoCellExpr.castBoundary (reseatPathInv_reseatPath sourcePath).symm
          (reseatPathInv_reseatPath targetPath).symm cell :=
  reseatCellInvReseatCellFueled cell.size cell (Nat.le_refl _)

/-! ## B2 — the reconstructed-signature reflection (the `reflect` hypothesis discharged) -/

/-- ★★ **The reconstructed-signature reflection** — a bespoke saturated convertibility between the `reseatCell`
IMAGES reflects back to a reconstructed convertibility between the ORIGINALS.  The BACKWARD transport
`reseatConvBackward` lands on the `reseatCellInv (reseatCell ..)` images; the CELL round-trip
`reseatCellInv_reseatCell` rewrites both onto a shared boundary cast, which `saturatedConvOver_castBoundaryStrip`
strips.  Modes are pinned to `⟨0⟩` first (the sole `Fin 1` inhabitant).  This inhabits the `reflect` hypothesis of
`monadReconstructedDecisionViaReflection` UNCONDITIONALLY. -/
theorem reseatReflect {sourceMode targetMode : Fin 1}
    {sourcePath targetPath : ModalityPath monadComputad.toModeGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver monadModeSignature MonadLawRel (reseatCell cellAlpha) (reseatCell cellBeta)) :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed cellAlpha cellBeta := by
  obtain rfl : sourceMode = (⟨0, by decide⟩ : Fin 1) := (finOneEqZero sourceMode).symm
  obtain rfl : targetMode = (⟨0, by decide⟩ : Fin 1) := (finOneEqZero targetMode).symm
  have back : SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
      (RawTwoCellExpr.castBoundary (reseatPathInv_reseatPath sourcePath).symm
        (reseatPathInv_reseatPath targetPath).symm cellAlpha)
      (RawTwoCellExpr.castBoundary (reseatPathInv_reseatPath sourcePath).symm
        (reseatPathInv_reseatPath targetPath).symm cellBeta) := by
    rw [← reseatCellInv_reseatCell cellAlpha, ← reseatCellInv_reseatCell cellBeta]
    exact reseatConvBackward conv
  exact saturatedConvOver_castBoundaryStrip _ _ back

/-! ## B3 — the UNCONDITIONAL reseated reconstructed-signature decider -/

/-- ★★ **The reseated reconstructed-signature decider, UNCONDITIONAL.**  A total
`DecidableSaturatedConvForRel monadComputad.toModeSignature MonadLawRelReconstructed`: the isFalse leg ships via the
forward transport (`monadReconRefutes`, roundtrip-free), the isTrue leg via the reflection `reseatReflect` (the
backward transport composed with the cell round-trip).  The `reflect` hypothesis of
`monadReconstructedDecisionViaReflection` is now discharged, so this decides EVERY reconstructed parallel pair. -/
def monadReconstructedDecision :
    DecidableSaturatedConvForRel monadComputad.toModeSignature MonadLawRelReconstructed :=
  monadReconstructedDecisionViaReflection (fun conv => reseatReflect conv)

/-! ## B3 — both verdicts LIVE on real reconstructed cells -/

/-- ★★ **The isTrue verdict, via the discharged REFLECTION on genuinely reconstructed cells** — the two
reconstructed associativity foldings `mu . (mu |> t)` / `mu . (t <| mu)` (`reconAssocLeftCell` /
`reconAssocRightCell`, NOT the `reseatCellInv`-of-bespoke variants) ARE saturated convertible over the
reconstructed signature.  Discharged by `reseatReflect` on the shipped bespoke associativity conv `reconAssocConv`
(their `reseatCell`-images), exercising the cell round-trip.  The isTrue leg the unconditional decider now
supplies. -/
theorem reconAssocReflectsTrue :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
      reconAssocLeftCell reconAssocRightCell :=
  reseatReflect reconAssocConv

/-- ★★ **The isTrue verdict on the reconstructed left-unit law, via the reflection** — the reconstructed left-unit
composite `mu . (eta |> t)` reflects to `id_t`.  Discharged by `reseatReflect` on the shipped bespoke left-unit
conv `reconLeftUnitConv`.  A second concrete convertible pair routed through the reflection. -/
theorem reconLeftUnitReflectsTrue :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
      reconLeftUnitCell reconIdTCell :=
  reseatReflect reconLeftUnitConv

/-- ★★ **The isFalse verdict, roundtrip-free** — the two reconstructed monad faces δ₁ / δ₀ are NOT convertible.
Re-anchored here (the shipped `reconFacesDecideFalse`, the forward-transport isFalse leg) so both verdicts of the
unconditional decider stand together on real reconstructed cells. -/
theorem reconFacesReflectFalse :
    ¬ SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
        reconFaceDeltaOne reconFaceDeltaZero :=
  reconFacesDecideFalse

/-- Non-vacuity of the cell round-trip on a real reconstructed cell — the reconstructed multiplication 2-cell
`reconMu` round-trips to its boundary cast. -/
theorem reseatCellInv_reseatCell_reconMu :
    reseatCellInv (reseatCell reconMu)
      = RawTwoCellExpr.castBoundary
          (reseatPathInv_reseatPath monadComputadReconstructedTT).symm
          (reseatPathInv_reseatPath monadComputadReconstructedT).symm reconMu :=
  reseatCellInv_reseatCell reconMu

/-! ## Honesty markers -/

/-- ★★ **Honesty marker (`true`) — the CELL round-trip node SHIPS (MODE-ADMIT-INV-N3, B1).**  `reseatCellInv
(reseatCell cell) = castBoundary .. cell` (`reseatCellInv_reseatCell`) is BUILT zero-axiom over the fixed `⟨0⟩ ⟨0⟩`
endpoints, via structural cell-size fuel (`reseatCellInvReseatCellFueled`) with the middle-mode pins in the two
whisker steps (`reseatCellInvReseatCellWhiskerLeftStep` / `reseatCellInvReseatCellWhiskerRightStep`), assembling the
shipped PATH node (`reseatPathInv_reseatPath`) and GEN node (`reseatGenInv_reseatGen`) over the whole
`RawTwoCellExpr` grammar (`gen` via `genTransportCast`, `id` via `castBoundaryId`, `vcomp` via `castBoundaryVcomp`,
the whiskers reconciling the forward `reseatPath_composePath` cast against the backward `reseatPathInv_composePath`
cast through `ReseatCastKit`).  All `Eq.rec` / no `HEq`, STRUCTURAL.  Non-vacuous on the real reconstructed cell
`reconMu` (`reseatCellInv_reseatCell_reconMu`).  `= true`. -/
def fxRecon_hasCellRoundTrip : Bool := true

/-- ★★ **Honesty marker (`true`) — the reconstructed-signature REFLECTION is DISCHARGED (B2).**  `reseatReflect`
(bespoke conv between the `reseatCell` images ⟹ reconstructed conv between the originals) is inhabited
UNCONDITIONALLY: the backward transport `reseatConvBackward` lands on the `reseatCellInv (reseatCell ..)` images,
the cell round-trip `reseatCellInv_reseatCell` rewrites both onto a shared boundary cast, and
`saturatedConvOver_castBoundaryStrip` strips it.  This inhabits the `reflect` hypothesis of
`monadReconstructedDecisionViaReflection`.  `= true`. -/
def fxRecon_hasReflection : Bool := true

/-- ★★ **Honesty marker (`true`) — the UNCONDITIONAL reseated reconstructed-signature decider SHIPS (B3, the #2229
milestone).**  `monadReconstructedDecision` is a total `DecidableSaturatedConvForRel monadComputad.toModeSignature
MonadLawRelReconstructed` with NO hypothesis: the isFalse leg via the forward transport (`monadReconRefutes`,
roundtrip-free), the isTrue leg via the discharged reflection `reseatReflect` (backward transport ∘ cell
round-trip).  Definitionally built on the shipped bespoke `monadSaturatedTwoCellDecision` it runs internally.  Both
verdicts LIVE on real reconstructed cells: isTrue on the
associativity foldings and the left-unit law (`reconAssocReflectsTrue` / `reconLeftUnitReflectsTrue`, via the
reflection) and isFalse on the two separating monad faces (`reconFacesReflectFalse`, roundtrip-free).  This flips
`fxAmalgInverse_hasReseatedReconstructionDecider` / `fxAmalg_hasReconstructionDecoderReseat` /
`fxModeAdmit_hasWiredInheritancePipeline`.

RETIREMENT-ENABLER NOTE (honest): this is the UNCONDITIONAL-DECIDER milestone, NOT island dissolution.  The decider
still transitively imports `WalkingMonad/MonadWordProblem` (the only bespoke-free monad decider,
`decideSaturatedConvOverMonadNative`, itself imports it for the conv-free `one_le_cellSize`), and the `SaturatedOver
→ MonadSaturatedConv` + `monadRelationFamily → monadSaturatedTwoCellDecision` root pins are UNTOUCHED.  So the
DeciderReseat bespoke-symbol dependency being discharged is NECESSARY-not-SUFFICIENT: deletion count this round is
ZERO — exactly as `Table/LedgerR1` sequenced #2229.  `= true`. -/
def fxRecon_hasUnconditionalReconstructionDecider : Bool := true

end FX1Poly.Polygraph.Amalgam
