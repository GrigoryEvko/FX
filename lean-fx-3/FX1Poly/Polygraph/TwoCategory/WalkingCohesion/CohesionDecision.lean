import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionModalityFragment
import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionPointsToPieces

/-! # WalkingCohesion/CohesionDecision — local posetality (thinness) and the decision modulo it (the honest wall)

The cohesion walker's decidability route is THINNESS, exactly as `WalkingIdempotent`: if every hom is a poset
(at most one 2-cell between parallel 1-cells) then the word problem is the boundary-existence check and the
decision is `isTrue` unconditionally.  This file states that as `CohesionThinness`, packages the decision assembly
that consumes it (complete and zero-axiom), ships the GENUINE thinness instances (the per-modality collapses +
the shared-`flat` snake coherence), and — HONESTLY — leaves the FULL thinness as the named residual.

## What genuinely closes vs the honest wall

  * The decision ASSEMBLY (`decideCohesionConvViaThinness`) is complete and zero-axiom: supplying thinness decides
    every parallel pair (always `isTrue`), exactly `WalkingIdempotent`'s `decideIdempotentConvViaThinness`.
  * GENUINE thinness INSTANCES are proved (from `CohesionModalityFragment`): the three modality endo-homs collapse,
    idempotence doing real work; the shared-central-`flat` snakes cohere.  The thin FRAGMENT is real.
  * The FULL `CohesionLocalPosetality` is NOT inhabited.  Unlike `WalkingIdempotent` (whose single-letter
    `monadTPower` normal form let `normalizeFull` inhabit thinness outright), the cohesion walker has THREE letters
    coupled by the string, and the CROSS-modality homs carry the points-to-pieces transform
    (`CohesionPointsToPieces`), which the presentation does NOT force to be thin (nLab: model-dependently
    non-invertible; the walking adjoint triple's own completeness is open).  So the FULL decision is the honest
    wall — shipped MODULO posetality, with the residual exhibited, NOT forced.

Raw Lean 4 + Init; the assembly is `Decidable`-plumbing over the `Prop` relation, so every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## Local posetality (thinness) -/

/-- ★ **Local posetality (thinness)** of the walking cohesion mode theory: ANY two parallel free 2-cells are
convertible — every hom is a poset with at most one 2-cell.  This is the genuine remaining content; the decision
below consumes it.  It is PROVED on the thin fragment (`CohesionModalityFragment`) and left as the residual on the
cross-modality homs (`CohesionPointsToPieces`). -/
def CohesionThinness : Prop :=
  ∀ {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr cohesionModeSignature sourcePath targetPath),
    CohesionSaturatedTwoCellConv cellA cellB

/-- The walking cohesion mode theory's **local-posetality** package — the thinness collapse the decision needs.
Mirrors `IdempotentMonadLocalPosetality`: a single field whose full mechanization is the residual (the
cross-modality thinness the points-to-pieces transform obstructs). -/
structure CohesionLocalPosetality where
  /-- All parallel free 2-cells are convertible (at most one 2-cell per hom). -/
  allParallelConv : CohesionThinness

/-! ## The decision modulo thinness -/

/-- ★ **Decide walking-cohesion saturated convertibility via thinness.**  Given local posetality, any parallel
pair is convertible, so the decision is `isTrue` unconditionally.  Complete and zero-axiom — the `isFalse` branch
never occurs because there are no non-convertible parallel pairs. -/
def decideCohesionConvViaThinness (posetality : CohesionLocalPosetality)
    {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr cohesionModeSignature sourcePath targetPath) :
    Decidable (CohesionSaturatedTwoCellConv cellA cellB) :=
  isTrue (posetality.allParallelConv cellA cellB)

/-- The walking cohesion mode theory's **saturated 2-cell word-problem interface**: saturated convertibility is
decidable on every parallel pair of free 2-cells. -/
abbrev CohesionDecidableSaturatedTwoCellConvFor : Type :=
  {sourceMode targetMode : CohesionMode} →
  {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode} →
  (cellA cellB : RawTwoCellExpr cohesionModeSignature sourcePath targetPath) →
  Decidable (CohesionSaturatedTwoCellConv cellA cellB)

/-- ★ **The walking cohesion mode theory's saturated 2-cell word problem, modulo local posetality.**  Supplying the
thinness collapse inhabits the full saturated decision interface — it decides EVERY parallel pair. -/
@[reducible] def cohesionSaturatedWordProblemModuloPosetality
    (posetality : CohesionLocalPosetality) : CohesionDecidableSaturatedTwoCellConvFor :=
  fun cellA cellB => decideCohesionConvViaThinness posetality cellA cellB

/-! ## Non-vacuity: a genuine identification + a genuine separation -/

/-- ★ **Genuine identification** (idempotence doing real work): the two `shape ⇒ shape` unit composites are
convertible DIRECTLY through the shape idempotence law — a size-4 parallel pair whose collapse is CONTENT, not
definitional.  Were thinness supplied, the decision would return `isTrue` on this pair; here it is proved outright
by the thin fragment, so the decision is non-vacuous. -/
theorem cohesionDecision_genuineIdentification :
    CohesionSaturatedTwoCellConv cohesionShapeLeftUnitCell cohesionShapeRightUnitCell :=
  cohesionShapeUnitComposites_viaIdempotence

/-- ★ **Genuine separation / non-degeneracy**: the three cohesive modalities are DISTINCT 1-cells, and the
points-to-pieces transform is a genuine 2-cell over the DISTINCT boundary `flat ⇒ shape` — so the walker is NOT a
degenerate single-modality collapse, and the decision problem is non-trivial (populated cross-modality homs the
per-modality thin fragment does not reach). -/
theorem cohesionDecision_genuineSeparation :
    cohesionShape ≠ cohesionFlat ∧ cohesionFlat ≠ cohesionSharp ∧ cohesionShape ≠ cohesionSharp ∧
      cohesionFlat ≠ cohesionShape :=
  ⟨cohesionShape_ne_flat, cohesionFlat_ne_sharp, cohesionShape_ne_sharp,
    cohesionPointsToPieces_crossModality⟩

/-- Smoke: were thinness supplied, the decision fires — `decideCohesionConvViaThinness` on any parallel pair is
`isTrue`.  (Stated as a function OF a posetality witness, so it is honest that the FULL decision is modulo the
residual — no unproven `isTrue` is manufactured; only the thin fragment is proved outright above.) -/
theorem decideCohesion_isTrue_ofPosetality (posetality : CohesionLocalPosetality) :
    ∀ {sourceMode targetMode : CohesionMode}
      {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
      (cellA cellB : RawTwoCellExpr cohesionModeSignature sourcePath targetPath),
      CohesionSaturatedTwoCellConv cellA cellB :=
  fun cellA cellB => posetality.allParallelConv cellA cellB

/-! ## Honesty markers -/

/-- ★ **ESTABLISHED — the decision assembly modulo thinness + the thin fragment.**  The saturated decision of the
walking cohesion mode theory is shipped MODULO the local-posetality collapse (`CohesionLocalPosetality`): the
assembly (`decideCohesionConvViaThinness` / `cohesionSaturatedWordProblemModuloPosetality`) is complete and
zero-axiom, and GENUINE thinness instances are proved — the three modality endo-homs collapse (idempotence doing
real work, `CohesionModalityFragment`), the shared-`flat` snakes cohere (`cohesionFlatSnakesCohere`), and the
decision is non-vacuous (`cohesionDecision_genuineIdentification` + `cohesionDecision_genuineSeparation`).
`= true`. -/
def fxCohesion_hasDecisionAssemblyModuloThinness : Bool := true

/-- ★★ **Honesty marker — the COHESION QUADRUPLE DECISION is the honest WALL (NOT flipped).**  The FULL local
posetality `CohesionThinness` (EVERY parallel pair convertible — hence a TOTAL `decideCohesionConv`) is NOT
inhabited.  The thin FRAGMENT is real (per-modality collapses + the shared-`flat` coherence), but the CROSS-modality
homs carry the points-to-pieces transform `flat ⇒ shape` (`CohesionPointsToPieces`), which the presentation does
NOT force to be thin: the idempotence collapses touch only modality-internal power-tower faces, and semantically
(nLab) the transform is model-dependently non-invertible (an equivalence only in infinitesimal cohesion / under
Aufhebung `♯∅ ≃ ∅`).  So the FULL decision is gated on the SAME cross-modality-thinness collapse the walking
adjoint triple leaves open (`fxString_hasAdjointTripleCompleteness = false`).  This lane ships the presentation, the
soundness (the saturated congruence), the thin fragment, and the EXACT residual (the transform), and does NOT force
a global thinness claim.  The downstream Axis `fxMode_hasCohesionModalityComputation` remains gated on this exact
residual.  `= false`. -/
def fxCohesion_hasCohesionQuadrupleDecision : Bool := false

end FX1Poly.Polygraph
