import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionSeed
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality

/-! # WalkingCohesion/CohesionSaturatedConv — the saturated 2-cell convertibility of the idempotent cohesion string

The walking-cohesion seed (`CohesionSeed`) posits the ten generators (three (co)monads plus two string
adjunctions); a COHESION mode theory is those generators SUBJECT to the (co)monad laws, the three IDEMPOTENCE
collapses, and the FOUR triangle identities.  This file ships the SATURATED 2-cell convertibility: the completed
free-strict-2-category convertibility (`TwoCellConvFull`, embedded by `ofFull`) augmented with

  * the shape / sharp MONAD laws (left-unit, right-unit, associativity — 3 each),
  * the flat COMONAD laws (left-counit, right-counit, coassociativity — 3),
  * the THREE idempotence collapses (well-(co)pointedness):
      `shapeUnit ▷ shape ≈ shape ◁ shapeUnit`  (shape monad idempotent),
      `flatCounit ▷ flat ≈ flat ◁ flatCounit`  (flat comonad idempotent — the DUAL well-copointed equation),
      `sharpUnit ▷ sharp ≈ sharp ◁ sharpUnit`  (sharp monad idempotent),
  * the FOUR adjoint-string triangle identities — two per adjunction (`ʃ ⊣ ♭` on shape and on flat; `♭ ⊣ ♯` on
    flat and on sharp), `flat` being the CENTRAL 1-cell straightened by TWO triangles,

made a genuine congruence by the four one-hole congruence closures plus `refl` / `symm` / `trans`.

## Why idempotence + the string is exactly the cohesion mode theory

nLab (*flat modality*): shape ʃ and sharp ♯ are idempotent MONADS, flat ♭ an idempotent COMONAD, coupled as
`ʃ ⊣ ♭ ⊣ ♯`.  The idempotence collapses are Street's / nLab's *idempotent monad* condition (well-pointedness
`η_{TT} = T η_T`) and its comonad dual; Rijke–Shulman–Spitters (*Modalities in HoTT*): idempotent modalities are
property-like, hence form a POSET — the thinness the decision consumes.  The two `flat`-triangles are the walking
adjoint triple's shared-central coupling (`WalkingString/StringSaturatedConv`), now carrying flat's comonad
structure on top.

Raw Lean 4 + Init; the relation is an inductive `Prop`, its witnesses are constructors, so every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The generating 2-cells embedded as free cells -/

/-- The shape unit `η^ʃ : id ⇒ shape` as a free 2-cell. -/
def cohesionShapeUnitCell :
    RawTwoCellExpr cohesionModeSignature
      (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionShape :=
  RawTwoCellExpr.gen CohesionTwoCell.shapeUnit

/-- The shape multiplication `μ^ʃ : shape·shape ⇒ shape` as a free 2-cell. -/
def cohesionShapeMulCell : RawTwoCellExpr cohesionModeSignature cohesionShapeShape cohesionShape :=
  RawTwoCellExpr.gen CohesionTwoCell.shapeMul

/-- The flat counit `ε^♭ : flat ⇒ id` as a free 2-cell. -/
def cohesionFlatCounitCell :
    RawTwoCellExpr cohesionModeSignature cohesionFlat
      (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) :=
  RawTwoCellExpr.gen CohesionTwoCell.flatCounit

/-- The flat comultiplication `δ^♭ : flat ⇒ flat·flat` as a free 2-cell. -/
def cohesionFlatComulCell : RawTwoCellExpr cohesionModeSignature cohesionFlat cohesionFlatFlat :=
  RawTwoCellExpr.gen CohesionTwoCell.flatComul

/-- The sharp unit `η^♯ : id ⇒ sharp` as a free 2-cell. -/
def cohesionSharpUnitCell :
    RawTwoCellExpr cohesionModeSignature
      (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionSharp :=
  RawTwoCellExpr.gen CohesionTwoCell.sharpUnit

/-- The sharp multiplication `μ^♯ : sharp·sharp ⇒ sharp` as a free 2-cell. -/
def cohesionSharpMulCell : RawTwoCellExpr cohesionModeSignature cohesionSharpSharp cohesionSharp :=
  RawTwoCellExpr.gen CohesionTwoCell.sharpMul

/-- The lower unit `η : id ⇒ shape·flat` (`ʃ ⊣ ♭`) as a free 2-cell. -/
def cohesionUnitShapeFlatCell :
    RawTwoCellExpr cohesionModeSignature
      (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionShapeFlat :=
  RawTwoCellExpr.gen CohesionTwoCell.unitShapeFlat

/-- The lower counit `ε : flat·shape ⇒ id` (`ʃ ⊣ ♭`) as a free 2-cell. -/
def cohesionCounitShapeFlatCell :
    RawTwoCellExpr cohesionModeSignature cohesionFlatShape
      (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) :=
  RawTwoCellExpr.gen CohesionTwoCell.counitShapeFlat

/-- The upper unit `η' : id ⇒ flat·sharp` (`♭ ⊣ ♯`) as a free 2-cell. -/
def cohesionUnitFlatSharpCell :
    RawTwoCellExpr cohesionModeSignature
      (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionFlatSharp :=
  RawTwoCellExpr.gen CohesionTwoCell.unitFlatSharp

/-- The upper counit `ε' : sharp·flat ⇒ id` (`♭ ⊣ ♯`) as a free 2-cell. -/
def cohesionCounitFlatSharpCell :
    RawTwoCellExpr cohesionModeSignature cohesionSharpFlat
      (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) :=
  RawTwoCellExpr.gen CohesionTwoCell.counitFlatSharp

/-! ## The identity 2-cells the laws collapse to -/

/-- The identity 2-cell on `shape`. -/
def cohesionShapeIdCell : RawTwoCellExpr cohesionModeSignature cohesionShape cohesionShape :=
  RawTwoCellExpr.id (signature := cohesionModeSignature) cohesionShape

/-- The identity 2-cell on `flat`. -/
def cohesionFlatIdCell : RawTwoCellExpr cohesionModeSignature cohesionFlat cohesionFlat :=
  RawTwoCellExpr.id (signature := cohesionModeSignature) cohesionFlat

/-- The identity 2-cell on `sharp`. -/
def cohesionSharpIdCell : RawTwoCellExpr cohesionModeSignature cohesionSharp cohesionSharp :=
  RawTwoCellExpr.id (signature := cohesionModeSignature) cohesionSharp

/-! ## The two idempotence faces of each modality -/

/-- **`shapeUnit ▷ shape`** `: shape ⇒ shape·shape` — the shape unit whiskered on the RIGHT by `shape` (the first
idempotence face of the shape monad). -/
def cohesionShapeEtaRightWhiskerCell : RawTwoCellExpr cohesionModeSignature cohesionShape cohesionShapeShape :=
  RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionShape cohesionShapeUnitCell

/-- **`shape ◁ shapeUnit`** `: shape ⇒ shape·shape` — the shape unit whiskered on the LEFT by `shape` (the second
idempotence face); shape idempotence identifies it with `cohesionShapeEtaRightWhiskerCell`. -/
def cohesionShapeEtaLeftWhiskerCell : RawTwoCellExpr cohesionModeSignature cohesionShape cohesionShapeShape :=
  RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionShape cohesionShapeUnitCell

/-- **`flatCounit ▷ flat`** `: flat·flat ⇒ flat` — the flat counit whiskered on the RIGHT by `flat` (the first
DUAL idempotence face of the flat comonad). -/
def cohesionFlatEpsRightWhiskerCell : RawTwoCellExpr cohesionModeSignature cohesionFlatFlat cohesionFlat :=
  RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionFlat cohesionFlatCounitCell

/-- **`flat ◁ flatCounit`** `: flat·flat ⇒ flat` — the flat counit whiskered on the LEFT by `flat` (the second
DUAL idempotence face); flat idempotence (well-copointedness `ε_{FF} = F ε_F`) identifies the two. -/
def cohesionFlatEpsLeftWhiskerCell : RawTwoCellExpr cohesionModeSignature cohesionFlatFlat cohesionFlat :=
  RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionFlat cohesionFlatCounitCell

/-- **`sharpUnit ▷ sharp`** `: sharp ⇒ sharp·sharp` — the first idempotence face of the sharp monad. -/
def cohesionSharpEtaRightWhiskerCell : RawTwoCellExpr cohesionModeSignature cohesionSharp cohesionSharpSharp :=
  RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionSharp cohesionSharpUnitCell

/-- **`sharp ◁ sharpUnit`** `: sharp ⇒ sharp·sharp` — the second idempotence face of the sharp monad. -/
def cohesionSharpEtaLeftWhiskerCell : RawTwoCellExpr cohesionModeSignature cohesionSharp cohesionSharpSharp :=
  RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionSharp cohesionSharpUnitCell

/-! ## The (co)monad-law composites -/

/-- The length-3 composite `shape·shape·shape` — the source of the shape associativity composites. -/
def cohesionShapeShapeShape : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  composePath cohesionShapeShape cohesionShape

/-- The length-3 composite `flat·flat·flat` — the target of the flat coassociativity composites. -/
def cohesionFlatFlatFlat : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  composePath cohesionFlatFlat cohesionFlat

/-- The length-3 composite `sharp·sharp·sharp` — the source of the sharp associativity composites. -/
def cohesionSharpSharpSharp : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  composePath cohesionSharpSharp cohesionSharp

/-- **`μ^ʃ ∘ (η^ʃ ▷ shape)`** `: shape ⇒ shape` — the shape left-unit composite. -/
def cohesionShapeLeftUnitCell : RawTwoCellExpr cohesionModeSignature cohesionShape cohesionShape :=
  RawTwoCellExpr.vcomp cohesionShapeEtaRightWhiskerCell cohesionShapeMulCell

/-- **`μ^ʃ ∘ (shape ◁ η^ʃ)`** `: shape ⇒ shape` — the shape right-unit composite. -/
def cohesionShapeRightUnitCell : RawTwoCellExpr cohesionModeSignature cohesionShape cohesionShape :=
  RawTwoCellExpr.vcomp cohesionShapeEtaLeftWhiskerCell cohesionShapeMulCell

/-- **`μ^ʃ ∘ (μ^ʃ ▷ shape)`** `: shape·shape·shape ⇒ shape` — the left-associativity composite. -/
def cohesionShapeAssocLeftCell : RawTwoCellExpr cohesionModeSignature cohesionShapeShapeShape cohesionShape :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionShape cohesionShapeMulCell)
    cohesionShapeMulCell

/-- **`μ^ʃ ∘ (shape ◁ μ^ʃ)`** `: shape·shape·shape ⇒ shape` — the right-associativity composite. -/
def cohesionShapeAssocRightCell : RawTwoCellExpr cohesionModeSignature cohesionShapeShapeShape cohesionShape :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionShape cohesionShapeMulCell)
    cohesionShapeMulCell

/-- **`(ε^♭ ▷ flat) ∘ δ^♭`** `: flat ⇒ flat` — the flat left-counit composite. -/
def cohesionFlatLeftCounitCell : RawTwoCellExpr cohesionModeSignature cohesionFlat cohesionFlat :=
  RawTwoCellExpr.vcomp cohesionFlatComulCell cohesionFlatEpsRightWhiskerCell

/-- **`(flat ◁ ε^♭) ∘ δ^♭`** `: flat ⇒ flat` — the flat right-counit composite. -/
def cohesionFlatRightCounitCell : RawTwoCellExpr cohesionModeSignature cohesionFlat cohesionFlat :=
  RawTwoCellExpr.vcomp cohesionFlatComulCell cohesionFlatEpsLeftWhiskerCell

/-- **`(δ^♭ ▷ flat) ∘ δ^♭`** `: flat ⇒ flat·flat·flat` — the left-coassociativity composite. -/
def cohesionFlatCoassocLeftCell : RawTwoCellExpr cohesionModeSignature cohesionFlat cohesionFlatFlatFlat :=
  RawTwoCellExpr.vcomp cohesionFlatComulCell
    (RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionFlat cohesionFlatComulCell)

/-- **`(flat ◁ δ^♭) ∘ δ^♭`** `: flat ⇒ flat·flat·flat` — the right-coassociativity composite. -/
def cohesionFlatCoassocRightCell : RawTwoCellExpr cohesionModeSignature cohesionFlat cohesionFlatFlatFlat :=
  RawTwoCellExpr.vcomp cohesionFlatComulCell
    (RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionFlat cohesionFlatComulCell)

/-- **`μ^♯ ∘ (η^♯ ▷ sharp)`** `: sharp ⇒ sharp` — the sharp left-unit composite. -/
def cohesionSharpLeftUnitCell : RawTwoCellExpr cohesionModeSignature cohesionSharp cohesionSharp :=
  RawTwoCellExpr.vcomp cohesionSharpEtaRightWhiskerCell cohesionSharpMulCell

/-- **`μ^♯ ∘ (sharp ◁ η^♯)`** `: sharp ⇒ sharp` — the sharp right-unit composite. -/
def cohesionSharpRightUnitCell : RawTwoCellExpr cohesionModeSignature cohesionSharp cohesionSharp :=
  RawTwoCellExpr.vcomp cohesionSharpEtaLeftWhiskerCell cohesionSharpMulCell

/-- **`μ^♯ ∘ (μ^♯ ▷ sharp)`** `: sharp·sharp·sharp ⇒ sharp` — the sharp left-associativity composite. -/
def cohesionSharpAssocLeftCell : RawTwoCellExpr cohesionModeSignature cohesionSharpSharpSharp cohesionSharp :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionSharp cohesionSharpMulCell)
    cohesionSharpMulCell

/-- **`μ^♯ ∘ (sharp ◁ μ^♯)`** `: sharp·sharp·sharp ⇒ sharp` — the sharp right-associativity composite. -/
def cohesionSharpAssocRightCell : RawTwoCellExpr cohesionModeSignature cohesionSharpSharpSharp cohesionSharp :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionSharp cohesionSharpMulCell)
    cohesionSharpMulCell

/-! ## The four adjoint-string snakes (zig-zags) -/

/-- The **lower `ʃ ⊣ ♭` snake on `shape`**: `(η ▷ shape) ⊟ (shape ◁ ε) : shape ⇒ shape` — `triangleShapeFlatOnShape`
straightens it to `id_shape`. -/
def cohesionShapeFlatSnakeOnShapeCell : RawTwoCellExpr cohesionModeSignature cohesionShape cohesionShape :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionShape cohesionUnitShapeFlatCell)
    (RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionShape cohesionCounitShapeFlatCell)

/-- The **lower `ʃ ⊣ ♭` snake on `flat`**: `(flat ◁ η) ⊟ (ε ▷ flat) : flat ⇒ flat` — `triangleShapeFlatOnFlat`
straightens it to `id_flat` (the FIRST of the two central-`flat` triangles). -/
def cohesionShapeFlatSnakeOnFlatCell : RawTwoCellExpr cohesionModeSignature cohesionFlat cohesionFlat :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionFlat cohesionUnitShapeFlatCell)
    (RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionFlat cohesionCounitShapeFlatCell)

/-- The **upper `♭ ⊣ ♯` snake on `flat`**: `(η' ▷ flat) ⊟ (flat ◁ ε') : flat ⇒ flat` — `triangleFlatSharpOnFlat`
straightens it to `id_flat` (the SECOND central-`flat` triangle, via the OTHER adjunction). -/
def cohesionFlatSharpSnakeOnFlatCell : RawTwoCellExpr cohesionModeSignature cohesionFlat cohesionFlat :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionFlat cohesionUnitFlatSharpCell)
    (RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionFlat cohesionCounitFlatSharpCell)

/-- The **upper `♭ ⊣ ♯` snake on `sharp`**: `(sharp ◁ η') ⊟ (ε' ▷ sharp) : sharp ⇒ sharp` —
`triangleFlatSharpOnSharp` straightens it to `id_sharp`. -/
def cohesionFlatSharpSnakeOnSharpCell : RawTwoCellExpr cohesionModeSignature cohesionSharp cohesionSharp :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionSharp cohesionUnitFlatSharpCell)
    (RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionSharp cohesionCounitFlatSharpCell)

/-! ## The saturated 2-cell convertibility -/

/-- ★ The **saturated 2-cell convertibility** of the walking (idempotent) cohesion mode theory: the completed
free-strict-2-category convertibility (`TwoCellConvFull`, embedded by `ofFull`) augmented with the shape / sharp
monad laws, the flat comonad laws, the THREE idempotence collapses, and the FOUR triangle identities, closed under
the four one-hole congruences and `refl`/`symm`/`trans` into a genuine congruence.  Two free 2-cells are equal AS
2-cells of the walking cohesion mode theory exactly when they are `CohesionSaturatedTwoCellConv`-related. -/
inductive CohesionSaturatedTwoCellConv :
    {sourceMode targetMode : CohesionMode} →
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode} →
    RawTwoCellExpr cohesionModeSignature sourcePath targetPath →
    RawTwoCellExpr cohesionModeSignature sourcePath targetPath → Prop where
  /-- Embed the completed free-strict-2-category convertibility (structural laws + interchange + whisker
  functoriality + congruence closure). -/
  | ofFull {sourceMode targetMode : CohesionMode}
      {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr cohesionModeSignature sourcePath targetPath} :
      TwoCellConvFull cohesionModeSignature cellAlpha cellBeta →
      CohesionSaturatedTwoCellConv cellAlpha cellBeta
  /-- The shape **left-unit** monad law `μ^ʃ ∘ (η^ʃ ▷ shape) ≈ id_shape`. -/
  | shapeLeftUnit : CohesionSaturatedTwoCellConv cohesionShapeLeftUnitCell cohesionShapeIdCell
  /-- The shape **right-unit** monad law `μ^ʃ ∘ (shape ◁ η^ʃ) ≈ id_shape`. -/
  | shapeRightUnit : CohesionSaturatedTwoCellConv cohesionShapeRightUnitCell cohesionShapeIdCell
  /-- The shape **associativity** monad law `μ^ʃ ∘ (μ^ʃ ▷ shape) ≈ μ^ʃ ∘ (shape ◁ μ^ʃ)`. -/
  | shapeAssoc : CohesionSaturatedTwoCellConv cohesionShapeAssocLeftCell cohesionShapeAssocRightCell
  /-- ★ The shape **idempotence** collapse `η^ʃ ▷ shape ≈ shape ◁ η^ʃ` (well-pointedness — shape is an idempotent
  monad). -/
  | shapeIdempotence :
      CohesionSaturatedTwoCellConv cohesionShapeEtaRightWhiskerCell cohesionShapeEtaLeftWhiskerCell
  /-- The flat **left-counit** comonad law `(ε^♭ ▷ flat) ∘ δ^♭ ≈ id_flat`. -/
  | flatLeftCounit : CohesionSaturatedTwoCellConv cohesionFlatLeftCounitCell cohesionFlatIdCell
  /-- The flat **right-counit** comonad law `(flat ◁ ε^♭) ∘ δ^♭ ≈ id_flat`. -/
  | flatRightCounit : CohesionSaturatedTwoCellConv cohesionFlatRightCounitCell cohesionFlatIdCell
  /-- The flat **coassociativity** comonad law `(δ^♭ ▷ flat) ∘ δ^♭ ≈ (flat ◁ δ^♭) ∘ δ^♭`. -/
  | flatCoassoc : CohesionSaturatedTwoCellConv cohesionFlatCoassocLeftCell cohesionFlatCoassocRightCell
  /-- ★ The flat **idempotence** collapse `ε^♭ ▷ flat ≈ flat ◁ ε^♭` (well-COpointedness `ε_{FF} = F ε_F` — flat is
  an idempotent comonad; the DUAL of the shape law). -/
  | flatIdempotence :
      CohesionSaturatedTwoCellConv cohesionFlatEpsRightWhiskerCell cohesionFlatEpsLeftWhiskerCell
  /-- The sharp **left-unit** monad law `μ^♯ ∘ (η^♯ ▷ sharp) ≈ id_sharp`. -/
  | sharpLeftUnit : CohesionSaturatedTwoCellConv cohesionSharpLeftUnitCell cohesionSharpIdCell
  /-- The sharp **right-unit** monad law `μ^♯ ∘ (sharp ◁ η^♯) ≈ id_sharp`. -/
  | sharpRightUnit : CohesionSaturatedTwoCellConv cohesionSharpRightUnitCell cohesionSharpIdCell
  /-- The sharp **associativity** monad law `μ^♯ ∘ (μ^♯ ▷ sharp) ≈ μ^♯ ∘ (sharp ◁ μ^♯)`. -/
  | sharpAssoc : CohesionSaturatedTwoCellConv cohesionSharpAssocLeftCell cohesionSharpAssocRightCell
  /-- ★ The sharp **idempotence** collapse `η^♯ ▷ sharp ≈ sharp ◁ η^♯` (sharp is an idempotent monad). -/
  | sharpIdempotence :
      CohesionSaturatedTwoCellConv cohesionSharpEtaRightWhiskerCell cohesionSharpEtaLeftWhiskerCell
  /-- The `ʃ ⊣ ♭` triangle on `shape` `(η ▷ shape) ⊟ (shape ◁ ε) ≈ id_shape`. -/
  | triangleShapeFlatOnShape :
      CohesionSaturatedTwoCellConv cohesionShapeFlatSnakeOnShapeCell cohesionShapeIdCell
  /-- The `ʃ ⊣ ♭` triangle on the central `flat` `(flat ◁ η) ⊟ (ε ▷ flat) ≈ id_flat`. -/
  | triangleShapeFlatOnFlat :
      CohesionSaturatedTwoCellConv cohesionShapeFlatSnakeOnFlatCell cohesionFlatIdCell
  /-- The `♭ ⊣ ♯` triangle on the central `flat` `(η' ▷ flat) ⊟ (flat ◁ ε') ≈ id_flat` (the OTHER `flat`
  triangle). -/
  | triangleFlatSharpOnFlat :
      CohesionSaturatedTwoCellConv cohesionFlatSharpSnakeOnFlatCell cohesionFlatIdCell
  /-- The `♭ ⊣ ♯` triangle on `sharp` `(sharp ◁ η') ⊟ (ε' ▷ sharp) ≈ id_sharp`. -/
  | triangleFlatSharpOnSharp :
      CohesionSaturatedTwoCellConv cohesionFlatSharpSnakeOnSharpCell cohesionSharpIdCell
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : CohesionMode}
      {oneCellF oneCellG oneCellH : ModalityPath cohesionGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr cohesionModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr cohesionModeSignature oneCellG oneCellH) :
      CohesionSaturatedTwoCellConv cellAlpha cellAlpha' →
      CohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : CohesionMode}
      {oneCellF oneCellG oneCellH : ModalityPath cohesionGraph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr cohesionModeSignature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr cohesionModeSignature oneCellG oneCellH} :
      CohesionSaturatedTwoCellConv cellBeta cellBeta' →
      CohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering (so a law fires whiskered by a 1-cell). -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : CohesionMode}
      (oneCell : ModalityPath cohesionGraph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath cohesionGraph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr cohesionModeSignature oneCellG oneCellH} :
      CohesionSaturatedTwoCellConv cellBeta cellBeta' →
      CohesionSaturatedTwoCellConv (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : CohesionMode}
      {oneCellF oneCellG : ModalityPath cohesionGraph sourceMode middleMode}
      (oneCell : ModalityPath cohesionGraph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr cohesionModeSignature oneCellF oneCellG} :
      CohesionSaturatedTwoCellConv cellAlpha cellAlpha' →
      CohesionSaturatedTwoCellConv (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')
  /-- Reflexivity. -/
  | refl {sourceMode targetMode : CohesionMode}
      {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
      (cell : RawTwoCellExpr cohesionModeSignature sourcePath targetPath) :
      CohesionSaturatedTwoCellConv cell cell
  /-- Symmetry. -/
  | symm {sourceMode targetMode : CohesionMode}
      {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr cohesionModeSignature sourcePath targetPath} :
      CohesionSaturatedTwoCellConv cellAlpha cellBeta → CohesionSaturatedTwoCellConv cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {sourceMode targetMode : CohesionMode}
      {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
      {cellAlpha cellBeta cellGamma : RawTwoCellExpr cohesionModeSignature sourcePath targetPath} :
      CohesionSaturatedTwoCellConv cellAlpha cellBeta → CohesionSaturatedTwoCellConv cellBeta cellGamma →
      CohesionSaturatedTwoCellConv cellAlpha cellGamma

/-! ## Embeddings and step lifting -/

/-- The free `TwoCellConv` (structural laws + interchange) lifts to the cohesion saturated relation. -/
theorem CohesionSaturatedTwoCellConv.ofConv {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr cohesionModeSignature sourcePath targetPath}
    (conv : TwoCellConv cohesionModeSignature cellAlpha cellBeta) :
    CohesionSaturatedTwoCellConv cellAlpha cellBeta :=
  CohesionSaturatedTwoCellConv.ofFull (TwoCellConvFull.ofConv conv)

/-- Lift a single 3-cell rewrite `TwoCellStep` into the cohesion saturated relation (via `ofConv`/`ofStep`). -/
theorem cohesionConvOfStep {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr cohesionModeSignature sourcePath targetPath}
    (step : TwoCellStep cohesionModeSignature cellAlpha cellBeta) :
    CohesionSaturatedTwoCellConv cellAlpha cellBeta :=
  CohesionSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep step)

/-! ## The saturation-flag witnesses -/

/-- ★ **Shape idempotence holds** — `η^ʃ ▷ shape ≈ shape ◁ η^ʃ`: shape is an idempotent monad. -/
theorem cohesionShapeIdempotenceHolds :
    CohesionSaturatedTwoCellConv cohesionShapeEtaRightWhiskerCell cohesionShapeEtaLeftWhiskerCell :=
  CohesionSaturatedTwoCellConv.shapeIdempotence

/-- ★ **Flat idempotence holds** — `ε^♭ ▷ flat ≈ flat ◁ ε^♭`: flat is an idempotent comonad (the DUAL). -/
theorem cohesionFlatIdempotenceHolds :
    CohesionSaturatedTwoCellConv cohesionFlatEpsRightWhiskerCell cohesionFlatEpsLeftWhiskerCell :=
  CohesionSaturatedTwoCellConv.flatIdempotence

/-- ★ **Sharp idempotence holds** — `η^♯ ▷ sharp ≈ sharp ◁ η^♯`: sharp is an idempotent monad. -/
theorem cohesionSharpIdempotenceHolds :
    CohesionSaturatedTwoCellConv cohesionSharpEtaRightWhiskerCell cohesionSharpEtaLeftWhiskerCell :=
  CohesionSaturatedTwoCellConv.sharpIdempotence

/-- ★★ **The shared-`flat` coherence.**  The two SYNTACTICALLY DISTINCT `flat ⇒ flat` snakes — the lower
`ʃ ⊣ ♭` snake and the upper `♭ ⊣ ♯` snake, both straightening the CENTRAL `flat` — are saturated-convertible to
EACH OTHER, both collapsing to `id_flat`.  This coherence lives in NEITHER single adjunction; it is the genuine
cross-level coupling the shared central `flat` creates (the cohesion analog of the walking adjoint triple's
`stringSnakeGlo_conv_stringSnakeGhi`). -/
theorem cohesionFlatSnakesCohere :
    CohesionSaturatedTwoCellConv cohesionShapeFlatSnakeOnFlatCell cohesionFlatSharpSnakeOnFlatCell :=
  CohesionSaturatedTwoCellConv.trans CohesionSaturatedTwoCellConv.triangleShapeFlatOnFlat
    (CohesionSaturatedTwoCellConv.symm CohesionSaturatedTwoCellConv.triangleFlatSharpOnFlat)

/-- Smoke: the shape idempotence law fires UNDER a left-whisker context — `flat ◁ (η^ʃ ▷ shape) ≈ flat ◁ (shape ◁
η^ʃ)` — exercising the congruence closure with the idempotence generator. -/
theorem cohesionShapeIdempotenceWhiskeredHolds :
    CohesionSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionFlat
        cohesionShapeEtaRightWhiskerCell)
      (RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionFlat
        cohesionShapeEtaLeftWhiskerCell) :=
  CohesionSaturatedTwoCellConv.whiskerLeftCongr _ CohesionSaturatedTwoCellConv.shapeIdempotence

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The SATURATED walking-cohesion 2-cell convertibility (`CohesionSaturatedTwoCellConv`) — the
completed free-strict-2-category convertibility plus the shape/sharp monad laws, the flat comonad laws, the THREE
idempotence collapses (`shapeIdempotence`/`flatIdempotence`/`sharpIdempotence`), and the FOUR triangle identities,
as a congruence — is shipped; all three idempotence laws hold, and the shared-central-`flat` coherence is genuine
(`cohesionFlatSnakesCohere`: the two distinct `flat ⇒ flat` snakes collapse to each other through `id_flat`, a
coherence in NEITHER single adjunction).  `= true`. -/
def fxCohesion_hasSaturatedConvWithIdempotence : Bool := true

end FX1Poly.Polygraph
