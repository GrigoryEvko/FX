import FX1Poly.Tier0.Mode.FreeTwoCellModel

/-! # mode-4 — per-modality adjoint strings (the RIGHT pillar: sharp / transpension / cohesion)

`mode-3` shipped the free 2-cell model (`RawTwoCellExpr`) and the 3-polygraph (`TwoCellStep` / `TwoCellConv`).
`mode-4` is the mode axis's RIGHT pillar — the ADJOINT structure on modalities: a modality `μ` may have a right
adjoint `⟨μ⟩` (its modal type former), which may itself have a further right adjoint, forming an ADJOINT STRING.
Lawvere cohesion is the canonical such string (shape ⊣ flat ⊣ sharp, `∫ ⊣ ♭ ⊣ ♯`); Nuyts transpension adds the
universal RIGHTMOST adjoint.

An adjunction `leftCell ⊣ rightCell` between two MODALITIES (1-cells of the mode 2-category) is given by a unit
2-cell `η : id ⇒ rightCell ∘ leftCell` and a counit `ε : leftCell ∘ rightCell ⇒ id` (in the mode theory's own
2-cells, i.e. `RawTwoCellExpr`), subject to the two TRIANGLE IDENTITIES.

## What this file ships (each piece zero-axiom)

  * **`TwoCellConv` is a CONGRUENCE** — `TwoCellConv.vcompCongrLeft` / `vcompCongrRight` / `whiskerLeftCongr` /
    `whiskerRightCongr`, lifting `mode-3`'s STEP-level congruence through the reflexive-symmetric-transitive
    closure (by induction on the conversion).  This completes `TwoCellConv` from "an equivalence relation" to "a
    congruence" — the property the triangle identities need to rewrite under composition.
  * **`FreeAdjunctionData`** — the adjunction DATA in the free 2-cell model: a left and a right modality with
    unit / counit 2-cells (cast-free, since the unit / counit boundaries are between parallel paths directly).
  * **`adjunctionSeedAdjunctionData`** — the canonical NON-DEGENERATE witness: the `mode-0` adjunction seed's
    unit / counit (`left ⊣ right` between the two modes) packaged as adjunction data.
  * **`identityFreeAdjunction`** + ★ **its two TRIANGLE IDENTITIES, PROVED up to `TwoCellConv`** — the identity
    modality is self-adjoint, and the snake equations hold by the `whisker{Left,Right}Id` and `vcompIdLeft`
    3-cells.  This is the genuine adjunction theorem: the 3-polygraph does real work discharging the coherence.

## What is DEFERRED (recorded by `= false` markers)

  * the GENERAL adjunction's triangle identities (the seed's `left ⊣ right`): the snake equations are ADDITIONAL
    relations beyond `mode-3`'s 3-polygraph (the free adjunction does not satisfy them) — saturating the system
    with the adjunction 3-cells + their convergence is `mode-9` (`hasAdjunctionTriangleSaturation = false`).
  * the SEMANTIC realizations — `∫ / ♭ / ♯` as presheaf endofunctors (Lawvere cohesion), the transpension `Ξ` as
    the universal right adjoint, sharp `♯` as the amazing right adjoint — are TYPE/CONTEXT-side functors,
    cross-axis (`mode-11` / `mode-13` / `type-11` / `fib`), deferred (`hasCohesiveModalityRealization = false`).

Zero external dependencies beyond the `mode-3` free 2-cell model.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## `TwoCellConv` is a congruence — lifting the step-level congruence through the closure -/

/-- `TwoCellConv` is a congruence in the LEFT factor of a vertical composite — the step-level
`TwoCellStep.vcompCongrLeft` lifted through the reflexive-symmetric-transitive closure. -/
theorem TwoCellConv.vcompCongrLeft {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
    (conv : TwoCellConv signature cellAlpha cellAlpha') :
    TwoCellConv signature (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      (RawTwoCellExpr.vcomp cellAlpha' cellBeta) := by
  induction conv with
  | ofStep step => exact TwoCellConv.ofStep (TwoCellStep.vcompCongrLeft cellBeta step)
  | refl _ => exact TwoCellConv.refl _
  | symm _ innerConv => exact TwoCellConv.symm innerConv
  | trans _ _ leftConv rightConv => exact TwoCellConv.trans leftConv rightConv

/-- `TwoCellConv` is a congruence in the RIGHT factor of a vertical composite. -/
theorem TwoCellConv.vcompCongrRight {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH}
    (conv : TwoCellConv signature cellBeta cellBeta') :
    TwoCellConv signature (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      (RawTwoCellExpr.vcomp cellAlpha cellBeta') := by
  induction conv with
  | ofStep step => exact TwoCellConv.ofStep (TwoCellStep.vcompCongrRight cellAlpha step)
  | refl _ => exact TwoCellConv.refl _
  | symm _ innerConv => exact TwoCellConv.symm innerConv
  | trans _ _ leftConv rightConv => exact TwoCellConv.trans leftConv rightConv

/-- `TwoCellConv` is a congruence under left whiskering. -/
theorem TwoCellConv.whiskerLeftCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH}
    (conv : TwoCellConv signature cellBeta cellBeta') :
    TwoCellConv signature (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
      (RawTwoCellExpr.whiskerLeft oneCell cellBeta') := by
  induction conv with
  | ofStep step => exact TwoCellConv.ofStep (TwoCellStep.whiskerLeftCongr oneCell step)
  | refl _ => exact TwoCellConv.refl _
  | symm _ innerConv => exact TwoCellConv.symm innerConv
  | trans _ _ leftConv rightConv => exact TwoCellConv.trans leftConv rightConv

/-- `TwoCellConv` is a congruence under right whiskering. -/
theorem TwoCellConv.whiskerRightCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG}
    (conv : TwoCellConv signature cellAlpha cellAlpha') :
    TwoCellConv signature (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
      (RawTwoCellExpr.whiskerRight oneCell cellAlpha') := by
  induction conv with
  | ofStep step => exact TwoCellConv.ofStep (TwoCellStep.whiskerRightCongr oneCell step)
  | refl _ => exact TwoCellConv.refl _
  | symm _ innerConv => exact TwoCellConv.symm innerConv
  | trans _ _ leftConv rightConv => exact TwoCellConv.trans leftConv rightConv

/-! ## Adjunction data in the free 2-cell model -/

/-- The **adjunction DATA** `leftCell ⊣ rightCell` between two modalities, in the free 2-cell model: a unit
2-cell `η : id ⇒ leftCell ∘ rightCell` and a counit `ε : rightCell ∘ leftCell ⇒ id` (diagrammatic order:
`composePath leftCell rightCell` is "leftCell then rightCell").  This is the DATA of an adjunction; the triangle
identities are the LAWS (see the markers — for the identity they are PROVED below, in general they are added
relations). -/
structure FreeAdjunctionData (signature : ModeSignature) {sourceMode targetMode : signature.graph.Mode}
    (leftCell : ModalityPath signature.graph sourceMode targetMode)
    (rightCell : ModalityPath signature.graph targetMode sourceMode) where
  /-- The unit `η : id ⇒ leftCell ∘ rightCell`. -/
  unit : RawTwoCellExpr signature (identityPath sourceMode) (composePath leftCell rightCell)
  /-- The counit `ε : rightCell ∘ leftCell ⇒ id`. -/
  counit : RawTwoCellExpr signature (composePath rightCell leftCell) (identityPath targetMode)

/-- ★ The canonical NON-DEGENERATE adjunction `left ⊣ right` of the `mode-0` adjunction seed: the unit and
counit GENERATORS (`adjunctionUnitTwoCell` / `adjunctionCounitTwoCell`) packaged as adjunction data between the
single-step modalities `left : base ⟶ tip` and `right : tip ⟶ base`. -/
def adjunctionSeedAdjunctionData :
    FreeAdjunctionData adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) (singletonModalityPath AdjunctionModality.right) where
  unit := adjunctionUnitTwoCell
  counit := adjunctionCounitTwoCell

/-- The IDENTITY modality is self-adjoint: `id ⊣ id` with the identity 2-cell as both unit and counit. -/
def identityFreeAdjunction (signature : ModeSignature) (mode : signature.graph.Mode) :
    FreeAdjunctionData signature (identityPath mode) (identityPath mode) where
  unit := RawTwoCellExpr.id (signature := signature) (identityPath mode)
  counit := RawTwoCellExpr.id (signature := signature) (identityPath mode)

/-! ## The triangle identities for the identity adjunction (proved up to `TwoCellConv`) -/

/-- ★ **Left triangle identity** for the identity self-adjunction: the snake `(η ▷ id) ⊟ (id ◁ ε)` is
CONVERTIBLE to the identity 2-cell.  Proved entirely from the 3-polygraph — both whiskered identities reduce by
`whisker{Right,Left}Id`, and the resulting `id ⊟ id` collapses by `vcompIdLeft` (using the derived
`TwoCellConv` congruence).  The 3-cells genuinely discharge the adjunction coherence. -/
theorem identityFreeAdjunction_leftTriangle (signature : ModeSignature) (mode : signature.graph.Mode) :
    TwoCellConv signature
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (identityPath mode)
          (RawTwoCellExpr.id (signature := signature) (identityPath mode)))
        (RawTwoCellExpr.whiskerLeft (identityPath mode)
          (RawTwoCellExpr.id (signature := signature) (identityPath mode))))
      (RawTwoCellExpr.id (signature := signature) (identityPath mode)) :=
  TwoCellConv.trans
    (TwoCellConv.vcompCongrLeft _
      (TwoCellConv.ofStep (TwoCellStep.whiskerRightId (identityPath mode) (identityPath mode))))
    (TwoCellConv.trans
      (TwoCellConv.vcompCongrRight _
        (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId (identityPath mode) (identityPath mode))))
      (TwoCellConv.ofStep
        (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id (signature := signature) (identityPath mode)))))

/-- ★ **Right triangle identity** for the identity self-adjunction — the dual snake, same proof shape. -/
theorem identityFreeAdjunction_rightTriangle (signature : ModeSignature) (mode : signature.graph.Mode) :
    TwoCellConv signature
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (identityPath mode)
          (RawTwoCellExpr.id (signature := signature) (identityPath mode)))
        (RawTwoCellExpr.whiskerRight (identityPath mode)
          (RawTwoCellExpr.id (signature := signature) (identityPath mode))))
      (RawTwoCellExpr.id (signature := signature) (identityPath mode)) :=
  TwoCellConv.trans
    (TwoCellConv.vcompCongrLeft _
      (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId (identityPath mode) (identityPath mode))))
    (TwoCellConv.trans
      (TwoCellConv.vcompCongrRight _
        (TwoCellConv.ofStep (TwoCellStep.whiskerRightId (identityPath mode) (identityPath mode))))
      (TwoCellConv.ofStep
        (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id (signature := signature) (identityPath mode)))))

/-! ## Honesty markers -/

/-- **Honesty marker.**  The triangle identities for a GENERAL adjunction (e.g. the seed's `left ⊣ right`) are
ADDITIONAL relations beyond `mode-3`'s 3-polygraph — the free adjunction does not satisfy the snake equations.
Saturating the system with the adjunction 3-cells and re-proving convergence is `mode-9`.  `= false`. -/
def fxMode_hasAdjunctionTriangleSaturation : Bool := false

/-- **Honesty marker.**  The SEMANTIC realizations of the adjoint string — `∫ / ♭ / ♯` as presheaf endofunctors
(Lawvere cohesion), the transpension `Ξ` as the universal right adjoint, sharp `♯` as the amazing right
adjoint — are TYPE/CONTEXT-side functors, cross-axis (`mode-11` / `mode-13` / `type-11` / `fib`), deferred.
`= false`. -/
def fxMode_hasCohesiveModalityRealization : Bool := false

end FX1Poly.Tier0
