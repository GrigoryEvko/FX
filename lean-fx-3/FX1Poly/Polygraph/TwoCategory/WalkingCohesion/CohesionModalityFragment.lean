import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionSaturatedConv

/-! # WalkingCohesion/CohesionModalityFragment — the THIN per-modality fragment (idempotence doing real work)

Each of the three cohesive modalities is, on its own, a WALKING IDEMPOTENT (co)monad instance
(`WalkingIdempotent`), hence LOCALLY POSETAL (thin) on its populated endo-homs.  This file ships the genuine,
idempotence-DRIVEN thinness instances that populate the thin fragment of the cohesion walker:

  * the SHAPE hom `shape ⇒ shape` collapses — `μ^ʃ ∘ (η^ʃ ▷ shape)` and `μ^ʃ ∘ (shape ◁ η^ʃ)` and `id_shape` are
    all mutually convertible, the two unit composites identified DIRECTLY through the shape idempotence law,
  * the FLAT hom `flat ⇒ flat` collapses — the DUAL, `(ε^♭ ▷ flat) ∘ δ^♭` and `(flat ◁ ε^♭) ∘ δ^♭` and `id_flat`,
    identified through the flat (comonad) idempotence law,
  * the SHARP hom `sharp ⇒ sharp` collapses — the same as shape.

Together with the shared-central-`flat` coherence (`cohesionFlatSnakesCohere`, in `CohesionSaturatedConv`) these
are the concrete, populated homs where the cohesion walker's local posetality is PROVED outright — the non-vacuous
core the decision consumes.  What is NOT covered here is the CROSS-modality thinness (the homs like `flat ⇒ shape`
where the points-to-pieces transform lives) — that is the residual (`CohesionPointsToPieces`).

By nLab (*flat modality*) + Rijke–Shulman–Spitters (*Modalities in HoTT*): idempotent modalities are property-like,
so each single modality's hom-poset collapses exactly as `WalkingIdempotent`'s `t ⇒ t` does.

Raw Lean 4 + Init; the collapses are constructor chains over the `Prop` relation, so every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

open CohesionSaturatedTwoCellConv

/-! ## Shape: the `shape ⇒ shape` hom collapses (idempotent monad) -/

/-- The shape left-unit composite `μ^ʃ ∘ (η^ʃ ▷ shape)` collapses to `id_shape` (the shape left-unit monad law). -/
theorem cohesionShapeLeftUnitConvId :
    CohesionSaturatedTwoCellConv cohesionShapeLeftUnitCell cohesionShapeIdCell :=
  CohesionSaturatedTwoCellConv.shapeLeftUnit

/-- The shape right-unit composite `μ^ʃ ∘ (shape ◁ η^ʃ)` collapses to `id_shape` (the shape right-unit monad law). -/
theorem cohesionShapeRightUnitConvId :
    CohesionSaturatedTwoCellConv cohesionShapeRightUnitCell cohesionShapeIdCell :=
  CohesionSaturatedTwoCellConv.shapeRightUnit

/-- ★ **Shape idempotence does real work**: the two `shape ⇒ shape` representatives `μ^ʃ ∘ (η^ʃ ▷ shape)` and
`μ^ʃ ∘ (shape ◁ η^ʃ)` are convertible DIRECTLY through the shape idempotence law (`η^ʃ ▷ shape ≈ shape ◁ η^ʃ` under
`vcompCongrLeft μ^ʃ`) — NOT only via the two unit laws.  A genuine, idempotence-driven thinness instance. -/
theorem cohesionShapeUnitComposites_viaIdempotence :
    CohesionSaturatedTwoCellConv cohesionShapeLeftUnitCell cohesionShapeRightUnitCell :=
  CohesionSaturatedTwoCellConv.vcompCongrLeft cohesionShapeMulCell
    CohesionSaturatedTwoCellConv.shapeIdempotence

/-- ★ **The shape hom `shape ⇒ shape` is thin on its representatives**: the two unit composites and `id_shape` are
all mutually convertible.  A concrete populated hom where the collapse is proved outright, shape idempotence doing
genuine work. -/
theorem cohesionShapeHom_thinOnRepresentatives :
    CohesionSaturatedTwoCellConv cohesionShapeLeftUnitCell cohesionShapeRightUnitCell ∧
      CohesionSaturatedTwoCellConv cohesionShapeLeftUnitCell cohesionShapeIdCell ∧
      CohesionSaturatedTwoCellConv cohesionShapeRightUnitCell cohesionShapeIdCell :=
  ⟨cohesionShapeUnitComposites_viaIdempotence, cohesionShapeLeftUnitConvId, cohesionShapeRightUnitConvId⟩

/-! ## Flat: the `flat ⇒ flat` hom collapses (idempotent COMONAD — the dual) -/

/-- The flat left-counit composite `(ε^♭ ▷ flat) ∘ δ^♭` collapses to `id_flat` (the flat left-counit comonad law). -/
theorem cohesionFlatLeftCounitConvId :
    CohesionSaturatedTwoCellConv cohesionFlatLeftCounitCell cohesionFlatIdCell :=
  CohesionSaturatedTwoCellConv.flatLeftCounit

/-- The flat right-counit composite `(flat ◁ ε^♭) ∘ δ^♭` collapses to `id_flat` (the flat right-counit comonad law). -/
theorem cohesionFlatRightCounitConvId :
    CohesionSaturatedTwoCellConv cohesionFlatRightCounitCell cohesionFlatIdCell :=
  CohesionSaturatedTwoCellConv.flatRightCounit

/-- ★ **Flat idempotence does real work (dually)**: the two `flat ⇒ flat` representatives `(ε^♭ ▷ flat) ∘ δ^♭` and
`(flat ◁ ε^♭) ∘ δ^♭` are convertible DIRECTLY through the flat (comonad) idempotence law (`ε^♭ ▷ flat ≈ flat ◁ ε^♭`
under `vcompCongrRight δ^♭`) — the DUAL of the shape instance, idempotence on the counit-whiskerings. -/
theorem cohesionFlatCounitComposites_viaIdempotence :
    CohesionSaturatedTwoCellConv cohesionFlatLeftCounitCell cohesionFlatRightCounitCell :=
  CohesionSaturatedTwoCellConv.vcompCongrRight cohesionFlatComulCell
    CohesionSaturatedTwoCellConv.flatIdempotence

/-- ★ **The flat hom `flat ⇒ flat` is thin on its representatives**: the two counit composites and `id_flat` are all
mutually convertible.  The coreflective (comonad) dual of the shape collapse. -/
theorem cohesionFlatHom_thinOnRepresentatives :
    CohesionSaturatedTwoCellConv cohesionFlatLeftCounitCell cohesionFlatRightCounitCell ∧
      CohesionSaturatedTwoCellConv cohesionFlatLeftCounitCell cohesionFlatIdCell ∧
      CohesionSaturatedTwoCellConv cohesionFlatRightCounitCell cohesionFlatIdCell :=
  ⟨cohesionFlatCounitComposites_viaIdempotence, cohesionFlatLeftCounitConvId, cohesionFlatRightCounitConvId⟩

/-! ## Sharp: the `sharp ⇒ sharp` hom collapses (idempotent monad) -/

/-- The sharp left-unit composite `μ^♯ ∘ (η^♯ ▷ sharp)` collapses to `id_sharp`. -/
theorem cohesionSharpLeftUnitConvId :
    CohesionSaturatedTwoCellConv cohesionSharpLeftUnitCell cohesionSharpIdCell :=
  CohesionSaturatedTwoCellConv.sharpLeftUnit

/-- The sharp right-unit composite `μ^♯ ∘ (sharp ◁ η^♯)` collapses to `id_sharp`. -/
theorem cohesionSharpRightUnitConvId :
    CohesionSaturatedTwoCellConv cohesionSharpRightUnitCell cohesionSharpIdCell :=
  CohesionSaturatedTwoCellConv.sharpRightUnit

/-- ★ **Sharp idempotence does real work**: the two `sharp ⇒ sharp` unit composites are convertible directly
through the sharp idempotence law. -/
theorem cohesionSharpUnitComposites_viaIdempotence :
    CohesionSaturatedTwoCellConv cohesionSharpLeftUnitCell cohesionSharpRightUnitCell :=
  CohesionSaturatedTwoCellConv.vcompCongrLeft cohesionSharpMulCell
    CohesionSaturatedTwoCellConv.sharpIdempotence

/-- ★ **The sharp hom `sharp ⇒ sharp` is thin on its representatives**. -/
theorem cohesionSharpHom_thinOnRepresentatives :
    CohesionSaturatedTwoCellConv cohesionSharpLeftUnitCell cohesionSharpRightUnitCell ∧
      CohesionSaturatedTwoCellConv cohesionSharpLeftUnitCell cohesionSharpIdCell ∧
      CohesionSaturatedTwoCellConv cohesionSharpRightUnitCell cohesionSharpIdCell :=
  ⟨cohesionSharpUnitComposites_viaIdempotence, cohesionSharpLeftUnitConvId, cohesionSharpRightUnitConvId⟩

/-! ## Honesty marker -/

/-- ★ **ESTABLISHED — the thin per-modality fragment.**  Each cohesive modality's endo-hom collapses on its
representatives, idempotence doing genuine work: the shape hom `shape ⇒ shape`
(`cohesionShapeHom_thinOnRepresentatives`, the two unit composites identified DIRECTLY through shape idempotence),
the flat hom `flat ⇒ flat` (`cohesionFlatHom_thinOnRepresentatives`, the coreflective comonad DUAL through flat
idempotence), and the sharp hom `sharp ⇒ sharp` (`cohesionSharpHom_thinOnRepresentatives`).  With the shared-`flat`
snake coherence (`cohesionFlatSnakesCohere`) these are the concrete, populated homs where the walker's local
posetality is PROVED — the non-vacuous thin fragment.  The cross-modality thinness (e.g. `flat ⇒ shape`, where the
points-to-pieces transform lives) is the residual (`CohesionPointsToPieces`).  `= true`. -/
def fxCohesion_hasModalityFragmentThinness : Bool := true

end FX1Poly.Polygraph
