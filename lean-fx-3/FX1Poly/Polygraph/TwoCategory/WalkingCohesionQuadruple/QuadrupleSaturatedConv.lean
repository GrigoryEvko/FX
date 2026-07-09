import FX1Poly.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleSeed
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality

/-! # WalkingCohesionQuadruple/QuadrupleSaturatedConv — the saturated 2-cell convertibility of the cohesion quadruple

The quadruple seed (`QuadrupleSeed`) posits nine generators (six adjunction units / counits plus three ff
inverses); the cohesion mode theory is those generators SUBJECT to the adjoint-quadruple relations.  This file
ships the SATURATED 2-cell convertibility: the completed free-strict-2-category convertibility (`TwoCellConvFull`,
embedded by `ofFull`) augmented with

  * the SIX adjoint triangle identities — two per adjunction, one straightening each of the two legs.  The shared
    legs `disc` and `gamma` are each straightened by TWO triangles (from the two adjunctions they straddle),
    exactly the walking adjoint triple's shared-central coupling extended to the quadruple,
  * the SIX fully-faithful ISO round-trip laws — `Disc` ff makes the lower counit and the middle unit isos
    (`counitLower ⊟ invCounitLower ≈ id`, `invCounitLower ⊟ counitLower ≈ id`, and the middle-unit pair), `coDisc`
    ff makes the upper counit an iso (`counitUpper ⊟ invCounitUpper ≈ id`, `invCounitUpper ⊟ counitUpper ≈ id`),

made a genuine congruence by the four one-hole closures plus `refl` / `symm` / `trans`.

## Why triangles + ff-isos is exactly the cohesion quadruple

Licata–Shulman (*Adjoint Logic with a 2-Category of Modes*): the cohesion interface is `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc`
with `Disc`, `coDisc` FULLY FAITHFUL.  nLab (*reflective subcategory*): a right adjoint is ff iff its counit is
iso; a left adjoint is ff iff its unit is iso — so the three ff-iso round-trips encode `Disc` ff (counit of
`Π₀ ⊣ Disc` and unit of `Disc ⊣ Γ`) and `coDisc` ff (counit of `Γ ⊣ coDisc`).  Making these units/counits isos is
exactly the "walking reflection" collapse (LSR): it forces the induced modalities `ʃ = pi0·disc`, `♭ = gamma·disc`,
`♯ = gamma·codisc` to be IDEMPOTENT (co)monads (the reflections' induced (co)monads).  This quadruple presentation
is the functor-level source of the induced modality presentation (`WalkingCohesion/CohesionSaturatedConv`).

Raw Lean 4 + Init; the relation is an inductive `Prop`, its witnesses are constructors, so every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The generating 2-cells embedded as free cells -/

/-- The lower unit `η : id_space ⇒ pi0·disc` (`Π₀ ⊣ Disc`) as a free 2-cell. -/
def quadUnitLowerCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) quadPi0Disc :=
  RawTwoCellExpr.gen QuadCohesionTwoCell.unitLower

/-- The lower counit `ε : disc·pi0 ⇒ id_pointSet` (`Π₀ ⊣ Disc`) as a free 2-cell. -/
def quadCounitLowerCell :
    RawTwoCellExpr quadCohesionModeSignature quadDiscPi0
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) :=
  RawTwoCellExpr.gen QuadCohesionTwoCell.counitLower

/-- The middle unit `η' : id_pointSet ⇒ disc·gamma` (`Disc ⊣ Γ`) as a free 2-cell. -/
def quadUnitMiddleCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadDiscGamma :=
  RawTwoCellExpr.gen QuadCohesionTwoCell.unitMiddle

/-- The middle counit `ε' : gamma·disc ⇒ id_space` (`Disc ⊣ Γ`) as a free 2-cell. -/
def quadCounitMiddleCell :
    RawTwoCellExpr quadCohesionModeSignature quadGammaDisc
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) :=
  RawTwoCellExpr.gen QuadCohesionTwoCell.counitMiddle

/-- The upper unit `η'' : id_space ⇒ gamma·codisc` (`Γ ⊣ coDisc`) as a free 2-cell. -/
def quadUnitUpperCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) quadGammaCodisc :=
  RawTwoCellExpr.gen QuadCohesionTwoCell.unitUpper

/-- The upper counit `ε'' : codisc·gamma ⇒ id_pointSet` (`Γ ⊣ coDisc`) as a free 2-cell. -/
def quadCounitUpperCell :
    RawTwoCellExpr quadCohesionModeSignature quadCodiscGamma
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) :=
  RawTwoCellExpr.gen QuadCohesionTwoCell.counitUpper

/-- The lower-counit inverse `id_pointSet ⇒ disc·pi0` (`Disc` ff) as a free 2-cell. -/
def quadInvCounitLowerCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadDiscPi0 :=
  RawTwoCellExpr.gen QuadCohesionTwoCell.invCounitLower

/-- The middle-unit inverse `disc·gamma ⇒ id_pointSet` (`Disc` ff) as a free 2-cell. -/
def quadInvUnitMiddleCell :
    RawTwoCellExpr quadCohesionModeSignature quadDiscGamma
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) :=
  RawTwoCellExpr.gen QuadCohesionTwoCell.invUnitMiddle

/-- The upper-counit inverse `id_pointSet ⇒ codisc·gamma` (`coDisc` ff) as a free 2-cell. -/
def quadInvCounitUpperCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadCodiscGamma :=
  RawTwoCellExpr.gen QuadCohesionTwoCell.invCounitUpper

/-! ## The identity 2-cells the laws collapse to -/

/-- The identity 2-cell on `pi0`. -/
def quadPi0IdCell : RawTwoCellExpr quadCohesionModeSignature quadPi0 quadPi0 :=
  RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadPi0

/-- The identity 2-cell on `disc`. -/
def quadDiscIdCell : RawTwoCellExpr quadCohesionModeSignature quadDisc quadDisc :=
  RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadDisc

/-- The identity 2-cell on `gamma`. -/
def quadGammaIdCell : RawTwoCellExpr quadCohesionModeSignature quadGamma quadGamma :=
  RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadGamma

/-- The identity 2-cell on `codisc`. -/
def quadCodiscIdCell : RawTwoCellExpr quadCohesionModeSignature quadCodisc quadCodisc :=
  RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadCodisc

/-- The identity 2-cell on `disc·pi0` (the lower-counit iso round-trip target). -/
def quadDiscPi0IdCell : RawTwoCellExpr quadCohesionModeSignature quadDiscPi0 quadDiscPi0 :=
  RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadDiscPi0

/-- The identity 2-cell on `disc·gamma` (the middle-unit iso round-trip target). -/
def quadDiscGammaIdCell : RawTwoCellExpr quadCohesionModeSignature quadDiscGamma quadDiscGamma :=
  RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadDiscGamma

/-- The identity 2-cell on `codisc·gamma` (the upper-counit iso round-trip target). -/
def quadCodiscGammaIdCell : RawTwoCellExpr quadCohesionModeSignature quadCodiscGamma quadCodiscGamma :=
  RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadCodiscGamma

/-- The identity 2-cell on `id_pointSet` (the target of the three "inverse-then-forward" iso round-trips). -/
def quadNilPointSetIdCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) :=
  RawTwoCellExpr.id (signature := quadCohesionModeSignature)
    (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)

/-! ## The six adjoint-triangle snakes (zig-zags), two per adjunction -/

/-- The **`Π₀ ⊣ Disc` snake on `pi0`**: `(unitLower ▷ pi0) ⊟ (pi0 ◁ counitLower) : pi0 ⇒ pi0` — `triPi0`
straightens it to `id_pi0`. -/
def quadTriPi0SnakeCell : RawTwoCellExpr quadCohesionModeSignature quadPi0 quadPi0 :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadUnitLowerCell)
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadCounitLowerCell)

/-- The **`Π₀ ⊣ Disc` snake on `disc`**: `(disc ◁ unitLower) ⊟ (counitLower ▷ disc) : disc ⇒ disc` — `triDiscLo`
straightens it to `id_disc` (the FIRST of the two `disc`-straightening triangles). -/
def quadTriDiscLoSnakeCell : RawTwoCellExpr quadCohesionModeSignature quadDisc quadDisc :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadUnitLowerCell)
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadCounitLowerCell)

/-- The **`Disc ⊣ Γ` snake on `disc`**: `(unitMiddle ▷ disc) ⊟ (disc ◁ counitMiddle) : disc ⇒ disc` — `triDiscHi`
straightens it to `id_disc` (the SECOND `disc`-straightening triangle, via the OTHER adjunction). -/
def quadTriDiscHiSnakeCell : RawTwoCellExpr quadCohesionModeSignature quadDisc quadDisc :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadUnitMiddleCell)
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadCounitMiddleCell)

/-- The **`Disc ⊣ Γ` snake on `gamma`**: `(gamma ◁ unitMiddle) ⊟ (counitMiddle ▷ gamma) : gamma ⇒ gamma` —
`triGammaLo` straightens it to `id_gamma` (the FIRST of the two `gamma`-straightening triangles). -/
def quadTriGammaLoSnakeCell : RawTwoCellExpr quadCohesionModeSignature quadGamma quadGamma :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadUnitMiddleCell)
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadCounitMiddleCell)

/-- The **`Γ ⊣ coDisc` snake on `gamma`**: `(unitUpper ▷ gamma) ⊟ (gamma ◁ counitUpper) : gamma ⇒ gamma` —
`triGammaHi` straightens it to `id_gamma` (the SECOND `gamma`-straightening triangle, via the OTHER adjunction). -/
def quadTriGammaHiSnakeCell : RawTwoCellExpr quadCohesionModeSignature quadGamma quadGamma :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitUpperCell)
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadCounitUpperCell)

/-- The **`Γ ⊣ coDisc` snake on `codisc`**: `(codisc ◁ unitUpper) ⊟ (counitUpper ▷ codisc) : codisc ⇒ codisc` —
`triCodisc` straightens it to `id_codisc`. -/
def quadTriCodiscSnakeCell : RawTwoCellExpr quadCohesionModeSignature quadCodisc quadCodisc :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadUnitUpperCell)
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadCounitUpperCell)

/-! ## The six fully-faithful iso round-trip composites -/

/-- `counitLower ⊟ invCounitLower : disc·pi0 ⇒ disc·pi0` — the lower-counit forward-then-back round-trip
(`Disc` ff). -/
def quadLowerCounitRoundRightCell : RawTwoCellExpr quadCohesionModeSignature quadDiscPi0 quadDiscPi0 :=
  RawTwoCellExpr.vcomp quadCounitLowerCell quadInvCounitLowerCell

/-- `invCounitLower ⊟ counitLower : id_pointSet ⇒ id_pointSet` — the lower-counit back-then-forward round-trip. -/
def quadLowerCounitRoundLeftCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) :=
  RawTwoCellExpr.vcomp quadInvCounitLowerCell quadCounitLowerCell

/-- `unitMiddle ⊟ invUnitMiddle : id_pointSet ⇒ id_pointSet` — the middle-unit forward-then-back round-trip
(`Disc` ff). -/
def quadMiddleUnitRoundRightCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) :=
  RawTwoCellExpr.vcomp quadUnitMiddleCell quadInvUnitMiddleCell

/-- `invUnitMiddle ⊟ unitMiddle : disc·gamma ⇒ disc·gamma` — the middle-unit back-then-forward round-trip. -/
def quadMiddleUnitRoundLeftCell : RawTwoCellExpr quadCohesionModeSignature quadDiscGamma quadDiscGamma :=
  RawTwoCellExpr.vcomp quadInvUnitMiddleCell quadUnitMiddleCell

/-- `counitUpper ⊟ invCounitUpper : codisc·gamma ⇒ codisc·gamma` — the upper-counit forward-then-back round-trip
(`coDisc` ff). -/
def quadUpperCounitRoundRightCell : RawTwoCellExpr quadCohesionModeSignature quadCodiscGamma quadCodiscGamma :=
  RawTwoCellExpr.vcomp quadCounitUpperCell quadInvCounitUpperCell

/-- `invCounitUpper ⊟ counitUpper : id_pointSet ⇒ id_pointSet` — the upper-counit back-then-forward round-trip. -/
def quadUpperCounitRoundLeftCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) :=
  RawTwoCellExpr.vcomp quadInvCounitUpperCell quadCounitUpperCell

/-! ## The saturated 2-cell convertibility -/

/-- ★ The **saturated 2-cell convertibility** of the walking cohesion quadruple: the completed
free-strict-2-category convertibility (`TwoCellConvFull`, embedded by `ofFull`) augmented with the SIX adjoint
triangle identities (two per adjunction, straightening each leg — `disc` and `gamma` each straightened by two) and
the SIX fully-faithful ISO round-trip laws (`Disc`, `coDisc` ff), closed under the four one-hole congruences and
`refl`/`symm`/`trans` into a genuine congruence.  Two free 2-cells are equal AS 2-cells of the walking cohesion
quadruple exactly when they are `QuadCohesionSaturatedTwoCellConv`-related. -/
inductive QuadCohesionSaturatedTwoCellConv :
    {sourceMode targetMode : QuadCohesionMode} →
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode} →
    RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath →
    RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath → Prop where
  /-- Embed the completed free-strict-2-category convertibility. -/
  | ofFull {sourceMode targetMode : QuadCohesionMode}
      {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath} :
      TwoCellConvFull quadCohesionModeSignature cellAlpha cellBeta →
      QuadCohesionSaturatedTwoCellConv cellAlpha cellBeta
  /-- The `Π₀ ⊣ Disc` triangle on `pi0` `(unitLower ▷ pi0) ⊟ (pi0 ◁ counitLower) ≈ id_pi0`. -/
  | triPi0 : QuadCohesionSaturatedTwoCellConv quadTriPi0SnakeCell quadPi0IdCell
  /-- The `Π₀ ⊣ Disc` triangle on `disc` `(disc ◁ unitLower) ⊟ (counitLower ▷ disc) ≈ id_disc`. -/
  | triDiscLo : QuadCohesionSaturatedTwoCellConv quadTriDiscLoSnakeCell quadDiscIdCell
  /-- The `Disc ⊣ Γ` triangle on `disc` `(unitMiddle ▷ disc) ⊟ (disc ◁ counitMiddle) ≈ id_disc` (the OTHER
  `disc` triangle). -/
  | triDiscHi : QuadCohesionSaturatedTwoCellConv quadTriDiscHiSnakeCell quadDiscIdCell
  /-- The `Disc ⊣ Γ` triangle on `gamma` `(gamma ◁ unitMiddle) ⊟ (counitMiddle ▷ gamma) ≈ id_gamma`. -/
  | triGammaLo : QuadCohesionSaturatedTwoCellConv quadTriGammaLoSnakeCell quadGammaIdCell
  /-- The `Γ ⊣ coDisc` triangle on `gamma` `(unitUpper ▷ gamma) ⊟ (gamma ◁ counitUpper) ≈ id_gamma` (the OTHER
  `gamma` triangle). -/
  | triGammaHi : QuadCohesionSaturatedTwoCellConv quadTriGammaHiSnakeCell quadGammaIdCell
  /-- The `Γ ⊣ coDisc` triangle on `codisc` `(codisc ◁ unitUpper) ⊟ (counitUpper ▷ codisc) ≈ id_codisc`. -/
  | triCodisc : QuadCohesionSaturatedTwoCellConv quadTriCodiscSnakeCell quadCodiscIdCell
  /-- ★ `Disc` ff: the lower counit is a SPLIT MONO `counitLower ⊟ invCounitLower ≈ id_{disc·pi0}`. -/
  | isoLowerCounitRight :
      QuadCohesionSaturatedTwoCellConv quadLowerCounitRoundRightCell quadDiscPi0IdCell
  /-- ★ `Disc` ff: the lower counit is a SPLIT EPI `invCounitLower ⊟ counitLower ≈ id_{id_pointSet}` — with the
  previous law, the lower counit is an ISO. -/
  | isoLowerCounitLeft :
      QuadCohesionSaturatedTwoCellConv quadLowerCounitRoundLeftCell quadNilPointSetIdCell
  /-- ★ `Disc` ff: the middle unit is a SPLIT MONO `unitMiddle ⊟ invUnitMiddle ≈ id_{id_pointSet}`. -/
  | isoMiddleUnitRight :
      QuadCohesionSaturatedTwoCellConv quadMiddleUnitRoundRightCell quadNilPointSetIdCell
  /-- ★ `Disc` ff: the middle unit is a SPLIT EPI `invUnitMiddle ⊟ unitMiddle ≈ id_{disc·gamma}` — with the
  previous law, the middle unit is an ISO. -/
  | isoMiddleUnitLeft :
      QuadCohesionSaturatedTwoCellConv quadMiddleUnitRoundLeftCell quadDiscGammaIdCell
  /-- ★ `coDisc` ff: the upper counit is a SPLIT MONO `counitUpper ⊟ invCounitUpper ≈ id_{codisc·gamma}`. -/
  | isoUpperCounitRight :
      QuadCohesionSaturatedTwoCellConv quadUpperCounitRoundRightCell quadCodiscGammaIdCell
  /-- ★ `coDisc` ff: the upper counit is a SPLIT EPI `invCounitUpper ⊟ counitUpper ≈ id_{id_pointSet}` — with the
  previous law, the upper counit is an ISO. -/
  | isoUpperCounitLeft :
      QuadCohesionSaturatedTwoCellConv quadUpperCounitRoundLeftCell quadNilPointSetIdCell
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : QuadCohesionMode}
      {oneCellF oneCellG oneCellH : ModalityPath quadCohesionGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr quadCohesionModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr quadCohesionModeSignature oneCellG oneCellH) :
      QuadCohesionSaturatedTwoCellConv cellAlpha cellAlpha' →
      QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : QuadCohesionMode}
      {oneCellF oneCellG oneCellH : ModalityPath quadCohesionGraph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr quadCohesionModeSignature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr quadCohesionModeSignature oneCellG oneCellH} :
      QuadCohesionSaturatedTwoCellConv cellBeta cellBeta' →
      QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering. -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : QuadCohesionMode}
      (oneCell : ModalityPath quadCohesionGraph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath quadCohesionGraph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr quadCohesionModeSignature oneCellG oneCellH} :
      QuadCohesionSaturatedTwoCellConv cellBeta cellBeta' →
      QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : QuadCohesionMode}
      {oneCellF oneCellG : ModalityPath quadCohesionGraph sourceMode middleMode}
      (oneCell : ModalityPath quadCohesionGraph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr quadCohesionModeSignature oneCellF oneCellG} :
      QuadCohesionSaturatedTwoCellConv cellAlpha cellAlpha' →
      QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')
  /-- Reflexivity. -/
  | refl {sourceMode targetMode : QuadCohesionMode}
      {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
      (cell : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath) :
      QuadCohesionSaturatedTwoCellConv cell cell
  /-- Symmetry. -/
  | symm {sourceMode targetMode : QuadCohesionMode}
      {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath} :
      QuadCohesionSaturatedTwoCellConv cellAlpha cellBeta → QuadCohesionSaturatedTwoCellConv cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {sourceMode targetMode : QuadCohesionMode}
      {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
      {cellAlpha cellBeta cellGamma : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath} :
      QuadCohesionSaturatedTwoCellConv cellAlpha cellBeta → QuadCohesionSaturatedTwoCellConv cellBeta cellGamma →
      QuadCohesionSaturatedTwoCellConv cellAlpha cellGamma

/-! ## Embeddings and step lifting -/

/-- The free `TwoCellConv` (structural laws + interchange) lifts to the quadruple saturated relation. -/
theorem QuadCohesionSaturatedTwoCellConv.ofConv {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath}
    (conv : TwoCellConv quadCohesionModeSignature cellAlpha cellBeta) :
    QuadCohesionSaturatedTwoCellConv cellAlpha cellBeta :=
  QuadCohesionSaturatedTwoCellConv.ofFull (TwoCellConvFull.ofConv conv)

/-- Lift a single 3-cell rewrite `TwoCellStep` into the quadruple saturated relation. -/
theorem quadCohesionConvOfStep {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath}
    (step : TwoCellStep quadCohesionModeSignature cellAlpha cellBeta) :
    QuadCohesionSaturatedTwoCellConv cellAlpha cellBeta :=
  QuadCohesionSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep step)

/-! ## The fully-faithful iso witnesses — the reflections' idempotency source -/

/-- ★ **`Disc` is fully faithful (lower counit iso).**  The lower counit `ε : disc·pi0 ⇒ id_pointSet` has a
two-sided inverse: `counitLower ⊟ invCounitLower ≈ id_{disc·pi0}` and `invCounitLower ⊟ counitLower ≈
id_{id_pointSet}`.  By nLab (*reflective subcategory*), the counit of `Π₀ ⊣ Disc` being iso is EXACTLY `Disc` ff,
which forces the induced comonad `♭ = Disc∘Γ`... and monad `ʃ = Disc∘Π₀` to be IDEMPOTENT. -/
theorem quadLowerCounitIsInvertible :
    QuadCohesionSaturatedTwoCellConv quadLowerCounitRoundRightCell quadDiscPi0IdCell ∧
      QuadCohesionSaturatedTwoCellConv quadLowerCounitRoundLeftCell quadNilPointSetIdCell :=
  ⟨QuadCohesionSaturatedTwoCellConv.isoLowerCounitRight,
    QuadCohesionSaturatedTwoCellConv.isoLowerCounitLeft⟩

/-- ★ **`Disc` is fully faithful (middle unit iso).**  The middle unit `η' : id_pointSet ⇒ disc·gamma` has a
two-sided inverse.  A left adjoint (here `Disc` in `Disc ⊣ Γ`) is ff iff its unit is iso — the SECOND witness that
`Disc` is fully faithful, coherent with the lower-counit one. -/
theorem quadMiddleUnitIsInvertible :
    QuadCohesionSaturatedTwoCellConv quadMiddleUnitRoundRightCell quadNilPointSetIdCell ∧
      QuadCohesionSaturatedTwoCellConv quadMiddleUnitRoundLeftCell quadDiscGammaIdCell :=
  ⟨QuadCohesionSaturatedTwoCellConv.isoMiddleUnitRight,
    QuadCohesionSaturatedTwoCellConv.isoMiddleUnitLeft⟩

/-- ★ **`coDisc` is fully faithful (upper counit iso).**  The upper counit `ε'' : codisc·gamma ⇒ id_pointSet` has
a two-sided inverse — `coDisc` (right adjoint of `Γ ⊣ coDisc`) is ff, forcing the induced monad `♯ = coDisc∘Γ`
idempotent. -/
theorem quadUpperCounitIsInvertible :
    QuadCohesionSaturatedTwoCellConv quadUpperCounitRoundRightCell quadCodiscGammaIdCell ∧
      QuadCohesionSaturatedTwoCellConv quadUpperCounitRoundLeftCell quadNilPointSetIdCell :=
  ⟨QuadCohesionSaturatedTwoCellConv.isoUpperCounitRight,
    QuadCohesionSaturatedTwoCellConv.isoUpperCounitLeft⟩

/-! ## The shared-leg snake coherences (the two triangles per shared leg cohere) -/

/-- ★★ **The shared-`disc` coherence.**  The two SYNTACTICALLY DISTINCT `disc ⇒ disc` snakes — the lower
`Π₀ ⊣ Disc` snake and the middle `Disc ⊣ Γ` snake, both straightening the shared leg `disc` — are
saturated-convertible to EACH OTHER, both collapsing to `id_disc`.  This coherence lives in NEITHER single
adjunction; it is the cross-adjunction coupling the shared `disc` creates (the functor-level analog of
`WalkingCohesion`'s `cohesionFlatSnakesCohere`). -/
theorem quadDiscSnakesCohere :
    QuadCohesionSaturatedTwoCellConv quadTriDiscLoSnakeCell quadTriDiscHiSnakeCell :=
  QuadCohesionSaturatedTwoCellConv.trans QuadCohesionSaturatedTwoCellConv.triDiscLo
    (QuadCohesionSaturatedTwoCellConv.symm QuadCohesionSaturatedTwoCellConv.triDiscHi)

/-- ★★ **The shared-`gamma` coherence.**  The two distinct `gamma ⇒ gamma` snakes — the middle `Disc ⊣ Γ` snake
and the upper `Γ ⊣ coDisc` snake, both straightening the shared leg `gamma` — cohere, both collapsing to
`id_gamma`.  The SECOND shared-leg coherence: the quadruple has TWO shared legs (`disc`, `gamma`), hence two such
cross-adjunction coherences (the induced string had only one, on the central `flat`). -/
theorem quadGammaSnakesCohere :
    QuadCohesionSaturatedTwoCellConv quadTriGammaLoSnakeCell quadTriGammaHiSnakeCell :=
  QuadCohesionSaturatedTwoCellConv.trans QuadCohesionSaturatedTwoCellConv.triGammaLo
    (QuadCohesionSaturatedTwoCellConv.symm QuadCohesionSaturatedTwoCellConv.triGammaHi)

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The SATURATED walking-cohesion-quadruple 2-cell convertibility
(`QuadCohesionSaturatedTwoCellConv`) — the completed free-strict-2-category convertibility plus the SIX adjoint
triangle identities and the SIX fully-faithful iso round-trip laws, as a congruence — is shipped; all three ff
legs are witnessed invertible (`quadLowerCounitIsInvertible` / `quadMiddleUnitIsInvertible` /
`quadUpperCounitIsInvertible`), and BOTH shared legs' snake pairs cohere (`quadDiscSnakesCohere`,
`quadGammaSnakesCohere`) — cross-adjunction coherences in NEITHER single adjunction.  `= true`. -/
def fxQuadCohesion_hasSaturatedConvWithFullyFaithful : Bool := true

end FX1Poly.Polygraph
