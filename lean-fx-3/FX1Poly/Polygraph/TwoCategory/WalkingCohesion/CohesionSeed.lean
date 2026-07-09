import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Model

/-! # WalkingCohesion/CohesionSeed — the walking COHESION seed: the idempotent adjoint string `ʃ ⊣ ♭ ⊣ ♯`

The presentation of the WALKING (idempotent) COHESION mode theory as a 2-computad (`ModeSignature`).  Where the
walking MONAD seed (`Computad/MonadSeed`) has one mode and one endo-1-cell `t`, and the walking ADJOINT-TRIPLE
seed (`WalkingString/StringSeed`) has two modes and a three-generator adjoint triple `F ⊣ G ⊣ H`, the walking
COHESION seed is the ONE-MODE idempotent form the Tier0 cohesion mode theory demands
(`Tier0/Mode/CohesionAdjointString`): ONE mode `point`, THREE endo-1-cell generators — the cohesive modalities

  * **`shape` (ʃ)** — an idempotent MONAD (reflective subuniverse), unit `id ⇒ shape`, mult `shape·shape ⇒ shape`,
  * **`flat` (♭)** — an idempotent COMONAD (coreflective subuniverse), counit `flat ⇒ id`, comult `flat ⇒ flat·flat`,
  * **`sharp` (♯)** — an idempotent MONAD, unit `id ⇒ sharp`, mult `sharp·sharp ⇒ sharp`,

coupled into the adjoint string `ʃ ⊣ ♭ ⊣ ♯` by TWO adjacent adjunctions SHARING the central `flat`:

  * the LOWER adjunction `ʃ ⊣ ♭` — unit `id ⇒ shape·flat`, counit `flat·shape ⇒ id`,
  * the UPPER adjunction `♭ ⊣ ♯` — unit `id ⇒ flat·sharp`, counit `sharp·flat ⇒ id`.

By nLab (*cohesive topos* / *cohesive (∞,1)-topos*): the adjoint quadruple `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` of the
global-sections geometric morphism induces, by composition, the adjoint string of MODALITIES `ʃ ⊣ ♭ ⊣ ♯` with
`ʃ = Disc∘Π₀`, `♭ = Disc∘Γ`, `♯ = coDisc∘Γ` — shape/sharp idempotent monads, flat an idempotent comonad
(*flat modality*).  Rijke–Shulman–Spitters (*Modalities in HoTT*, arXiv:1706.07526): these idempotent (property-like)
modalities form a POSET.  This seed is that presentation's 2-computad; the (co)monad laws, the idempotence
collapses, and the four triangle identities are the saturation relations (`CohesionSaturatedConv`).

## The cohesion adjoint-string boundary convention

Mirrors `WalkingString/StringSeed` (`FreeAdjunctionData`): a unit is `id ⇒ left·right`, a counit is
`right·left ⇒ id`.  For `ʃ ⊣ ♭` (`left = shape`, `right = flat`) the unit is `id ⇒ shape·flat`, the counit is
`flat·shape ⇒ id`; for `♭ ⊣ ♯` (`left = flat`, `right = sharp`) the unit is `id ⇒ flat·sharp`, the counit is
`sharp·flat ⇒ id`.  `flat` is the CENTRAL 1-cell (right adjoint below, left adjoint above), exactly the shared `G`
of the walking adjoint triple.

Generic presentation data (no mode-theory dependence), so it lives in the signature-free `Polygraph/` library.
Zero external dependencies beyond the free-2-cell model.  Raw Lean 4 + Init. -/

namespace FX1Poly.Polygraph

/-! ## The walking-cohesion quiver: one object, three endo-modality generators -/

/-- The single mode (0-cell) of the walking cohesion mode theory. -/
inductive CohesionMode where
  /-- The unique object. -/
  | point

/-- The three generating modalities (1-cells) of the walking cohesion mode theory — the cohesive modalities as
endo-1-cells `point ⟶ point`: the shape modality `ʃ`, the flat modality `♭`, and the sharp modality `♯`. -/
inductive CohesionModality : CohesionMode → CohesionMode → Type where
  /-- The shape modality `ʃ` (an idempotent monad). -/
  | shape : CohesionModality CohesionMode.point CohesionMode.point
  /-- The flat modality `♭` (an idempotent comonad). -/
  | flat : CohesionModality CohesionMode.point CohesionMode.point
  /-- The sharp modality `♯` (an idempotent monad). -/
  | sharp : CohesionModality CohesionMode.point CohesionMode.point

/-- The walking-cohesion quiver: one mode, three endo-modality generators. -/
def cohesionGraph : ModeGraph where
  Mode := CohesionMode
  Modality := CohesionModality

/-! ## The generating 1-cells and the composites the 2-cells live between -/

/-- The shape modality `ʃ` as the length-1 path. -/
def cohesionShape : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  singletonModalityPath CohesionModality.shape

/-- The flat modality `♭` as the length-1 path. -/
def cohesionFlat : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  singletonModalityPath CohesionModality.flat

/-- The sharp modality `♯` as the length-1 path. -/
def cohesionSharp : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  singletonModalityPath CohesionModality.sharp

/-- The composite `shape·shape` (length 2) — the source of the shape multiplication. -/
def cohesionShapeShape : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  composePath cohesionShape cohesionShape

/-- The composite `flat·flat` (length 2) — the target of the flat comultiplication. -/
def cohesionFlatFlat : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  composePath cohesionFlat cohesionFlat

/-- The composite `sharp·sharp` (length 2) — the source of the sharp multiplication. -/
def cohesionSharpSharp : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  composePath cohesionSharp cohesionSharp

/-- The composite `shape·flat` (length 2) — the target of the lower `ʃ ⊣ ♭` unit. -/
def cohesionShapeFlat : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  composePath cohesionShape cohesionFlat

/-- The composite `flat·shape` (length 2) — the source of the lower `ʃ ⊣ ♭` counit. -/
def cohesionFlatShape : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  composePath cohesionFlat cohesionShape

/-- The composite `flat·sharp` (length 2) — the target of the upper `♭ ⊣ ♯` unit. -/
def cohesionFlatSharp : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  composePath cohesionFlat cohesionSharp

/-- The composite `sharp·flat` (length 2) — the source of the upper `♭ ⊣ ♯` counit. -/
def cohesionSharpFlat : ModalityPath cohesionGraph CohesionMode.point CohesionMode.point :=
  composePath cohesionSharp cohesionFlat

/-! ## The generating 2-cells: three (co)monads plus two string adjunctions -/

/-- The generating 2-cells of the walking cohesion mode theory — the shape / sharp idempotent-monad units and
multiplications, the flat idempotent-comonad counit and comultiplication, and the four adjoint-string units /
counits (`ʃ ⊣ ♭` and `♭ ⊣ ♯`).  These are the GENERATORS only; the (co)monad laws, the three idempotence
collapses, and the four triangle identities are the saturation relations (`CohesionSaturatedConv`). -/
inductive CohesionTwoCell :
    {sourceMode targetMode : CohesionMode} →
    ModalityPath cohesionGraph sourceMode targetMode →
    ModalityPath cohesionGraph sourceMode targetMode → Type where
  /-- The **shape unit** `η^ʃ : id ⇒ shape` (arity `(0, 1)`). -/
  | shapeUnit : CohesionTwoCell (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionShape
  /-- The **shape multiplication** `μ^ʃ : shape·shape ⇒ shape` (arity `(2, 1)`). -/
  | shapeMul : CohesionTwoCell cohesionShapeShape cohesionShape
  /-- The **flat counit** `ε^♭ : flat ⇒ id` (arity `(1, 0)`) — flat is co-pointed. -/
  | flatCounit : CohesionTwoCell cohesionFlat (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point)
  /-- The **flat comultiplication** `δ^♭ : flat ⇒ flat·flat` (arity `(1, 2)`). -/
  | flatComul : CohesionTwoCell cohesionFlat cohesionFlatFlat
  /-- The **sharp unit** `η^♯ : id ⇒ sharp` (arity `(0, 1)`). -/
  | sharpUnit : CohesionTwoCell (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionSharp
  /-- The **sharp multiplication** `μ^♯ : sharp·sharp ⇒ sharp` (arity `(2, 1)`). -/
  | sharpMul : CohesionTwoCell cohesionSharpSharp cohesionSharp
  /-- The **lower unit** `η : id ⇒ shape·flat` of `ʃ ⊣ ♭` (arity `(0, 2)`, the lower CUP). -/
  | unitShapeFlat : CohesionTwoCell (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionShapeFlat
  /-- The **lower counit** `ε : flat·shape ⇒ id` of `ʃ ⊣ ♭` (arity `(2, 0)`, the lower CAP). -/
  | counitShapeFlat : CohesionTwoCell cohesionFlatShape (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point)
  /-- The **upper unit** `η' : id ⇒ flat·sharp` of `♭ ⊣ ♯` (arity `(0, 2)`, the upper CUP). -/
  | unitFlatSharp : CohesionTwoCell (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionFlatSharp
  /-- The **upper counit** `ε' : sharp·flat ⇒ id` of `♭ ⊣ ♯` (arity `(2, 0)`, the upper CAP). -/
  | counitFlatSharp : CohesionTwoCell cohesionSharpFlat (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point)

/-- ★ The **walking-cohesion mode signature** — the free 2-category on the idempotent adjoint string
`ʃ ⊣ ♭ ⊣ ♯`: one mode `point`, three endo-modality generators `shape`/`flat`/`sharp`, and the ten unit /
counit / multiplication / comultiplication 2-cell generators.  This is the seed the cohesion free-2-cell tower and
the saturated convertibility are instantiated at. -/
def cohesionModeSignature : ModeSignature where
  graph := cohesionGraph
  twoCell := fun firstPath secondPath => CohesionTwoCell firstPath secondPath

/-! ## Freeness smokes -/

/-- Smoke: `shape` is a length-1 1-cell. -/
theorem cohesionShape_length : cohesionShape.length = 1 := rfl

/-- Smoke: `shape·flat` is a length-2 1-cell. -/
theorem cohesionShapeFlat_length : cohesionShapeFlat.length = 2 := rfl

/-- Smoke: `sharp·flat` is a length-2 1-cell. -/
theorem cohesionSharpFlat_length : cohesionSharpFlat.length = 2 := rfl

/-- Smoke: the three cohesive modalities are DISTINCT 1-cells — `shape ≠ flat`.  The free construction separates
the generators, so the walker is NOT a degenerate collapse of the modalities into one. -/
theorem cohesionShape_ne_flat : cohesionShape ≠ cohesionFlat := by
  intro pathsEqual
  have generatorsEqual : CohesionModality.shape = CohesionModality.flat :=
    singletonModalityPath_injective pathsEqual
  nomatch generatorsEqual

/-- Smoke: `flat ≠ sharp` — the co-reflective modality is distinct from the upper reflective one. -/
theorem cohesionFlat_ne_sharp : cohesionFlat ≠ cohesionSharp := by
  intro pathsEqual
  have generatorsEqual : CohesionModality.flat = CohesionModality.sharp :=
    singletonModalityPath_injective pathsEqual
  nomatch generatorsEqual

/-- Smoke: `shape ≠ sharp` — the two ENDS of the adjoint string are distinct modalities. -/
theorem cohesionShape_ne_sharp : cohesionShape ≠ cohesionSharp := by
  intro pathsEqual
  have generatorsEqual : CohesionModality.shape = CohesionModality.sharp :=
    singletonModalityPath_injective pathsEqual
  nomatch generatorsEqual

end FX1Poly.Polygraph
