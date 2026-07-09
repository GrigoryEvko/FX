import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionDecision

/-! # WalkingCohesion/CohesionNonThinness — the free cohesion walker is NOT locally posetal (thinness REFUTED)

r1 (`CohesionDecision`) shipped the walking-cohesion decision MODULO local posetality (`CohesionThinness`), left
`CohesionLocalPosetality` uninhabited, and named the cross-modality thinness as the residual.  This r2 lane
SETTLES the residual with a machine-checked COUNTEREXAMPLE: the free walking-cohesion 2-category is **NOT thin**.
The thinness route is not merely unproven; it is provably DEAD.

## The refutation (a sound conv-invariant separating a parallel pair)

The obstruction the recon flagged is real and lives already at the UNIT hom `id ⇒ shape`.  Two parallel free
2-cells there:

  * the **shape monad unit** `η^ʃ = cohesionShapeUnitCell : id ⇒ shape` (Route 1, a bare generator),
  * the **lower-adjunction route** `η ⊟ (shape ◁ ε^♭) = cohesionShapeUnitViaLowerAdjunctionCell : id ⇒ shape`
    (Route 2, the lower `ʃ ⊣ ♭` unit `η : id ⇒ shape·flat` followed by the shape-whiskered flat COMONAD counit
    `ε^♭ : flat ⇒ id`; the target `shape·id` is definitionally `shape`, `composePath` recursing on its first path
    so the trailing `nil` erases on the nose).

Route 2 uses the ADJUNCTION unit `unitShapeFlat` and the COMONAD counit `flatCounit`; the triangle identity that
could straighten a `shape ⊣ flat` snake uses the ADJUNCTION counit `counitShapeFlat` (`flat·shape ⇒ id`), a
DIFFERENT generator whiskered on the OTHER side — so NO relation of the presentation connects Route 2 to Route 1.
The three idempotence collapses only touch modality-INTERNAL power-tower faces; and semantically (nLab
*points-to-pieces transform*) the cross-modality comparison is model-dependently non-invertible.  Hence the
presentation does NOT force these two parallel cells equal.

We make that non-connection MACHINE-CHECKED with a sound separating invariant — the `ℤ/2` (Boolean-XOR) DEGREE
homomorphism `genParity` weighting each generator, instantiated (`cohesionParity`) with the shape unit /
multiplication weighing `true` and every other generator `false`.  It is invariant under the WHOLE saturated
congruence: the structural laws / interchange / whisker functoriality rearrange generators (parity preserved by
`genParity_convFull`), and each cohesion law balances (`shapeUnit ^^ shapeMul = false = id`, every monad / comonad
/ triangle law collapses to `false`, idempotence keeps a single `shapeUnit`).  It computes `true` on `η^ʃ` and
`false` on Route 2 — so they are NOT convertible, and the hom `id ⇒ shape` is NOT a poset.

## Disposition (route B, decisive)

`CohesionThinness` is REFUTED (`cohesionNotLocallyPosetal : ¬ CohesionThinness`), hence `CohesionLocalPosetality`
is provably UNINHABITED (`cohesionLocalPosetality_uninhabited`).  The r1 decision assembly
(`decideCohesionConvViaThinness`) stays honest — it consumes a posetality witness that provably cannot exist, so
no `isTrue` is ever manufactured.  The cohesion quadruple decision therefore CANNOT go through thinness; the
remaining route is per-boundary FINITE HOM ENUMERATION (the walking-adjunction Δ/matching pattern), a separate
arc.  `fxCohesion_hasCohesionQuadrupleDecision` stays `false`, now for a PROVED reason.

Non-vacuity: the invariant is not the trivial everything-distinct one — it AGREES with a genuine r1 identification
(`cohesionShapeLeftUnitCell` and `cohesionShapeRightUnitCell`, convertible via shape idempotence, share parity
`false`), so it separates a genuinely-inconvertible pair while respecting a genuinely-convertible one.

Raw Lean 4 + Init; `genParity` is a structural `Bool` fold, the soundness is structural induction over the
`Prop` relations, the separation is `Bool.noConfusion` — every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The generic `ℤ/2` parity degree (any signature, any generator weighting) -/

/-- A four-fold XOR rearrangement — the interchange law's parity obligation, closed by exhaustive `Bool` casing. -/
private theorem xorMiddleFour (bitW bitX bitY bitZ : Bool) :
    (bitW.xor bitX).xor (bitY.xor bitZ) = (bitW.xor bitY).xor (bitX.xor bitZ) := by
  cases bitW <;> cases bitX <;> cases bitY <;> cases bitZ <;> rfl

/-- ★ The **parity degree** of a free 2-cell, over ANY signature and ANY generator weighting `weight`: a `ℤ/2`
(Boolean-XOR) homomorphism — a generator weighs `weight`, an identity weighs `false`, a vertical composite XORs
its factors, and whiskering is TRANSPARENT (a 1-cell action carries no generator content).  Structural recursion
over the five 2-cell constructors, constant `Bool` motive: `propext`-free. -/
def genParity {signature : ModeSignature}
    (weight : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      signature.twoCell sourcePath targetPath → Bool) :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Bool
  | _, _, _, _, .gen generator => weight generator
  | _, _, _, _, .id _ => false
  | _, _, _, _, .vcomp cellAlpha cellBeta => (genParity weight cellAlpha).xor (genParity weight cellBeta)
  | _, _, _, _, .whiskerLeft _ cellBeta => genParity weight cellBeta
  | _, _, _, _, .whiskerRight _ cellAlpha => genParity weight cellAlpha

/-- Parity is invisible to a boundary cast (`castBoundary` is `Eq.rec`, collapsing to the identity once its two
boundary equalities are substituted). -/
theorem genParity_castBoundary {signature : ModeSignature}
    (weight : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      signature.twoCell sourcePath targetPath → Bool)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    genParity weight (RawTwoCellExpr.castBoundary hsource htarget cell) = genParity weight cell := by
  cases hsource; cases htarget; rfl

/-- Parity is preserved by a single structural 3-cell rewrite `TwoCellStep` (identity absorption, associativity,
whisker-identity/distribution, congruences, and interchange) — the structural laws only rearrange generators. -/
theorem genParity_step {signature : ModeSignature}
    (weight : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      signature.twoCell sourcePath targetPath → Bool)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature cellAlpha cellBeta) :
    genParity weight cellAlpha = genParity weight cellBeta := by
  induction step with
  | vcompIdLeft _ => exact Bool.false_xor _
  | vcompIdRight _ => exact Bool.xor_false _
  | vcompAssoc _ _ _ => exact Bool.xor_assoc _ _ _
  | whiskerLeftId _ _ => rfl
  | whiskerRightId _ _ => rfl
  | whiskerLeftVcomp _ _ _ => rfl
  | whiskerRightVcomp _ _ _ => rfl
  | vcompCongrLeft _ _ ih => dsimp only [genParity]; rw [ih]
  | vcompCongrRight _ _ ih => dsimp only [genParity]; rw [ih]
  | whiskerLeftCongr _ _ ih => dsimp only [genParity]; exact ih
  | whiskerRightCongr _ _ ih => dsimp only [genParity]; exact ih
  | interchange _ _ _ _ =>
      dsimp only [genParity, RawTwoCellExpr.hcomp]
      exact xorMiddleFour _ _ _ _

/-- Parity is preserved by structural convertibility `TwoCellConv` (reflexive-symmetric-transitive closure). -/
theorem genParity_conv {signature : ModeSignature}
    (weight : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      signature.twoCell sourcePath targetPath → Bool)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature cellAlpha cellBeta) :
    genParity weight cellAlpha = genParity weight cellBeta := by
  induction conv with
  | ofStep step => exact genParity_step weight step
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- ★ Parity is preserved by the COMPLETED convertibility `TwoCellConvFull` (structural + whisker functoriality:
unit-whisker stripping, composite-whisker splitting, disjoint-whisker exchange — all same-generator, threaded
through boundary casts parity cannot see). -/
theorem genParity_convFull {signature : ModeSignature}
    (weight : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      signature.twoCell sourcePath targetPath → Bool)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature cellAlpha cellBeta) :
    genParity weight cellAlpha = genParity weight cellBeta := by
  induction convFull with
  | ofConv conv => exact genParity_conv weight conv
  | whiskerLeftUnit _ => rfl
  | whiskerRightUnit _ => rw [genParity_castBoundary]; rfl
  | whiskerLeftComp _ _ _ => rw [genParity_castBoundary]; rfl
  | whiskerRightComp _ _ _ => rw [genParity_castBoundary]; rfl
  | whiskerExchange _ _ _ => rw [genParity_castBoundary]; rfl
  | vcompCongrLeft _ _ ih => dsimp only [genParity]; rw [ih]
  | vcompCongrRight _ _ ih => dsimp only [genParity]; rw [ih]
  | whiskerLeftCongr _ _ ih => dsimp only [genParity]; exact ih
  | whiskerRightCongr _ _ ih => dsimp only [genParity]; exact ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## The cohesion generator weights and the instantiated parity -/

/-- The `ℤ/2` weight of each cohesion generator: the shape unit `η^ʃ` and multiplication `μ^ʃ` weigh `true`, every
other generator weighs `false`.  Full ten-constructor enumeration, constant `Bool` motive (a wildcard arm would
leak `propext`), so the weight is `propext`-free.  The choice satisfies every id-sided law: `shapeUnit` pairs with
`shapeMul` (both `true`, `true ^^ true = false = id`), and every other law's non-identity side weighs `false`. -/
def cohesionGeneratorParity {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    (generator : CohesionTwoCell sourcePath targetPath) : Bool :=
  match generator with
  | .shapeUnit => true
  | .shapeMul => true
  | .flatCounit => false
  | .flatComul => false
  | .sharpUnit => false
  | .sharpMul => false
  | .unitShapeFlat => false
  | .counitShapeFlat => false
  | .unitFlatSharp => false
  | .counitFlatSharp => false

/-- ★ The **cohesion parity degree** — `genParity` at the cohesion signature with the shape-unit weighting.  The
sound separating invariant that refutes thinness. -/
def cohesionParity {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr cohesionModeSignature sourcePath targetPath) : Bool :=
  genParity cohesionGeneratorParity cell

/-- ★ **Cohesion parity is a sound invariant of the saturated cohesion congruence.**  Convertible free 2-cells
have equal parity — the completed convertibility (`ofFull`, via `genParity_convFull`), every shape/sharp monad law,
flat comonad law, idempotence collapse, and adjoint-string triangle balances (each `rfl`), and the congruences
propagate.  Hence any parity DIFFERENCE proves non-convertibility. -/
theorem cohesionParity_satConv {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr cohesionModeSignature sourcePath targetPath}
    (conv : CohesionSaturatedTwoCellConv cellAlpha cellBeta) :
    cohesionParity cellAlpha = cohesionParity cellBeta := by
  induction conv with
  | ofFull convFull => exact genParity_convFull cohesionGeneratorParity convFull
  | shapeLeftUnit => rfl
  | shapeRightUnit => rfl
  | shapeAssoc => rfl
  | shapeIdempotence => rfl
  | flatLeftCounit => rfl
  | flatRightCounit => rfl
  | flatCoassoc => rfl
  | flatIdempotence => rfl
  | sharpLeftUnit => rfl
  | sharpRightUnit => rfl
  | sharpAssoc => rfl
  | sharpIdempotence => rfl
  | triangleShapeFlatOnShape => rfl
  | triangleShapeFlatOnFlat => rfl
  | triangleFlatSharpOnFlat => rfl
  | triangleFlatSharpOnSharp => rfl
  | vcompCongrLeft cellBeta _ ih => exact congrArg (fun bit => bit.xor (cohesionParity cellBeta)) ih
  | vcompCongrRight cellAlpha _ ih => exact congrArg (fun bit => (cohesionParity cellAlpha).xor bit) ih
  | whiskerLeftCongr _ _ ih => exact ih
  | whiskerRightCongr _ _ ih => exact ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## The separating parallel pair at the unit hom `id ⇒ shape` -/

/-- ★ The **lower-adjunction route to `shape`** `η ⊟ (shape ◁ ε^♭) : id ⇒ shape` — the lower `ʃ ⊣ ♭` unit
`η : id ⇒ shape·flat` followed by the shape-whiskered flat COMONAD counit `ε^♭ : flat ⇒ id`.  Its target
`shape·id` is definitionally `shape` (`composePath` recurses on its first path, so the trailing `nil` erases on
the nose), so it is genuinely PARALLEL to the shape monad unit `cohesionShapeUnitCell : id ⇒ shape`. -/
def cohesionShapeUnitViaLowerAdjunctionCell :
    RawTwoCellExpr cohesionModeSignature
      (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionShape :=
  RawTwoCellExpr.vcomp cohesionUnitShapeFlatCell
    (RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionShape cohesionFlatCounitCell)

/-- The shape monad unit has parity `true` (it IS the weighted generator `η^ʃ`). -/
theorem cohesionShapeUnit_parity : cohesionParity cohesionShapeUnitCell = true := rfl

/-- The lower-adjunction route has parity `false` (`unitShapeFlat ^^ flatCounit = false ^^ false`) — it uses
NEITHER shape unit nor shape multiplication. -/
theorem cohesionShapeUnitViaLowerAdjunction_parity :
    cohesionParity cohesionShapeUnitViaLowerAdjunctionCell = false := rfl

/-- ★★ **The two parallel `id ⇒ shape` cells are NOT convertible.**  The shape monad unit and the lower-adjunction
route sit over the SAME boundary yet carry different parity (`true` vs `false`), and parity is a sound congruence
invariant (`cohesionParity_satConv`) — so no chain of cohesion relations identifies them.  The unit hom `id ⇒
shape` is therefore NOT a poset: the free walker is not thin. -/
theorem cohesionShapeUnit_notConvertibleToLowerAdjunctionRoute :
    ¬ CohesionSaturatedTwoCellConv cohesionShapeUnitCell cohesionShapeUnitViaLowerAdjunctionCell := by
  intro conv
  have hParityEqual :
      cohesionParity cohesionShapeUnitCell = cohesionParity cohesionShapeUnitViaLowerAdjunctionCell :=
    cohesionParity_satConv conv
  rw [cohesionShapeUnit_parity, cohesionShapeUnitViaLowerAdjunction_parity] at hParityEqual
  exact Bool.noConfusion hParityEqual

/-! ## The refutation of thinness -/

/-- ★★★ **The free walking-cohesion 2-category is NOT locally posetal (thinness REFUTED).**  If every parallel
pair were convertible then in particular the shape monad unit and the lower-adjunction route would be — refuted by
`cohesionShapeUnit_notConvertibleToLowerAdjunctionRoute`.  The thinness route to the cohesion decision is not merely
unproven; it is provably DEAD. -/
theorem cohesionNotLocallyPosetal : ¬ CohesionThinness := by
  intro thinness
  exact cohesionShapeUnit_notConvertibleToLowerAdjunctionRoute
    (thinness cohesionShapeUnitCell cohesionShapeUnitViaLowerAdjunctionCell)

/-- ★ **The local-posetality package is provably UNINHABITED.**  `CohesionLocalPosetality` carries
`CohesionThinness`, which is false — so r1's `decideCohesionConvViaThinness` consumes a witness that cannot exist,
and no `isTrue` is ever manufactured from thinness.  The honest wall of r1 is now a PROVED wall. -/
theorem cohesionLocalPosetality_uninhabited : CohesionLocalPosetality → False :=
  fun posetality => cohesionNotLocallyPosetal posetality.allParallelConv

/-! ## Non-vacuity: the invariant is not the trivial everything-distinct one -/

/-- **Non-vacuity.**  The parity invariant AGREES with a genuine r1 identification: the two shape unit composites
`μ^ʃ ∘ (η^ʃ ▷ shape)` and `μ^ʃ ∘ (shape ◁ η^ʃ)` — convertible through shape idempotence
(`cohesionShapeUnitComposites_viaIdempotence`) — share parity `false`.  So `cohesionParity` respects a
genuinely-convertible pair while separating the genuinely-inconvertible unit/route pair; it is a real invariant,
not the degenerate one that distinguishes everything. -/
theorem cohesionParity_agreesOnGenuineIdentification :
    cohesionParity cohesionShapeLeftUnitCell = cohesionParity cohesionShapeRightUnitCell :=
  cohesionParity_satConv cohesionShapeUnitComposites_viaIdempotence

/-- **Non-vacuity, spelled out.**  The refutation is genuine and cross-cutting: the shape monad unit and the
lower-adjunction route are parallel (`id ⇒ shape`) with different parity (a genuine SEPARATION), the invariant
agrees on a genuine IDENTIFICATION, and the boundary generators `flat`, `shape` are distinct 1-cells (the walker is
no degenerate single-modality collapse). -/
theorem cohesionNonThinness_isNonVacuous :
    (cohesionParity cohesionShapeUnitCell = true ∧
      cohesionParity cohesionShapeUnitViaLowerAdjunctionCell = false) ∧
    cohesionParity cohesionShapeLeftUnitCell = cohesionParity cohesionShapeRightUnitCell ∧
    cohesionFlat ≠ cohesionShape :=
  ⟨⟨cohesionShapeUnit_parity, cohesionShapeUnitViaLowerAdjunction_parity⟩,
    cohesionParity_agreesOnGenuineIdentification, cohesionPointsToPieces_crossModality⟩

/-! ## Honesty markers -/

/-- ★★ **ESTABLISHED — thinness is REFUTED, the walker is provably not locally posetal.**  `= false`, backed by
`cohesionNotLocallyPosetal : ¬ CohesionThinness` (a sound `ℤ/2`-parity invariant separates the parallel shape
monad unit from the lower-adjunction route at the hom `id ⇒ shape`).  This is a decisive NEGATIVE disposition of
the cross-modality-thinness residual r1 named: the thinness route to the cohesion decision is provably dead, not
merely open. -/
def fxCohesion_isLocallyPosetal : Bool := false

/-- ★★ **ESTABLISHED — the thinness refutation ships.**  `= true`: `cohesionParity` is a machine-checked sound
congruence invariant (`cohesionParity_satConv`), it separates a genuine parallel pair
(`cohesionShapeUnit_notConvertibleToLowerAdjunctionRoute`), and it refutes both `CohesionThinness`
(`cohesionNotLocallyPosetal`) and the inhabitedness of `CohesionLocalPosetality`
(`cohesionLocalPosetality_uninhabited`), non-vacuously (`cohesionNonThinness_isNonVacuous`).  The cohesion
quadruple decision therefore cannot go via thinness; the remaining route is per-boundary finite hom enumeration
(the walking-adjunction Δ/matching pattern), a separate arc — so `fxCohesion_hasCohesionQuadrupleDecision` stays
`false`, now for a PROVED reason. -/
def fxCohesion_hasThinnessRefutation : Bool := true

end FX1Poly.Polygraph
