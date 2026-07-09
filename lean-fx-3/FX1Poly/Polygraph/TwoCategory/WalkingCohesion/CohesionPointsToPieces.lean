import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionSaturatedConv

/-! # WalkingCohesion/CohesionPointsToPieces — the points-to-pieces transform: the exact non-thin RESIDUAL

The thin per-modality fragment (`CohesionModalityFragment`) collapses each cohesive modality's ENDO-hom.  The
FULL walker's local posetality additionally needs the CROSS-modality homs to be thin — and there the
**points-to-pieces transform** lives, the genuine obstruction the literature flags.

## The transform

nLab (*points-to-pieces transform*): the composite `♭X ⟶ X ⟶ ʃX` (the flat counit `ε^♭` followed by the shape
unit `η^ʃ`), "the transformation from points to their pieces".  It is the modal shadow of punctual local
connectedness; the Tier0 mode theory already ships it as `CohesionAdjointQuadruple.piecesHavePoints`
(`shapeUnit ∘ flatCounit : ♭X → ʃX`).  In the polygraph walker it is the 2-cell
`cohesionPointsToPiecesCell = vcomp flatCounit shapeUnit : flat ⇒ shape`.

## Why it is the exact residual (literature-faithful, NOT forced)

nLab: "In infinitesimal cohesion the points-to-pieces transform is an EQUIVALENCE" — i.e. NOT an equivalence in
general cohesion; it is neither mono nor epi nor iso in general (it is epi iff "pieces have points", iso under
Aufhebung `♯∅ ≃ ∅`).  So whether `flat ⇒ shape` is THIN in the free walker is MODEL-DEPENDENT semantically and NOT
forced by the presentation: the three idempotence collapses only identify modality-INTERNAL power-tower faces
(`shape ⇒ shape·shape`, `flat·flat ⇒ flat`, ...), never a CROSS-modality comparison like `flat ⇒ shape`.  Hence:

  * the transform IS a genuine 2-cell (constructed, size 3, between the DISTINCT 1-cells `flat` and `shape`);
  * the modality-internal laws ACT on the hom (a flat-comonad-law detour collapses back onto it — the hom is
    populated and non-inert);
  * but whether `flat ⇒ shape` is THIN — hence whether the FULL cohesion walker is locally posetal — is NOT
    established.  It is the exact residual, epistemically the same status as the walking adjoint triple's open
    `fxString_hasAdjointTripleCompleteness = false` (whose Δ-like homs are already non-thin).  This lane does NOT
    flip a global thinness claim; it exhibits the transform and walls the residual honestly.

Raw Lean 4 + Init; the cell is a free composite and the identifications are constructor chains, so every
declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The points-to-pieces transform as a free 2-cell -/

/-- ★ The **points-to-pieces transform** `♭ ⟹ ʃ` — the flat counit `ε^♭ : flat ⇒ id` followed by the shape unit
`η^ʃ : id ⇒ shape`, i.e. `vcomp flatCounit shapeUnit : flat ⇒ shape`.  The modal shadow of "pieces have points"
(the walker incarnation of the Tier0 `piecesHavePoints : ♭X → ʃX`), the genuine cross-modality comparison. -/
def cohesionPointsToPiecesCell : RawTwoCellExpr cohesionModeSignature cohesionFlat cohesionShape :=
  RawTwoCellExpr.vcomp cohesionFlatCounitCell cohesionShapeUnitCell

/-- Smoke: the transform has `size 3` (a `vcomp` of the two generators `ε^♭` and `η^ʃ`) — a genuine composite, not
a bare atom. -/
theorem cohesionPointsToPiecesCell_size : cohesionPointsToPiecesCell.size = 3 := rfl

/-- ★ The transform is a genuine CROSS-modality 2-cell: its boundary 1-cells `flat` and `shape` are DISTINCT (the
free construction separates the generators), so `flat ⇒ shape` is a genuinely different hom from any modality's
endo-hom — exactly the region the per-modality thin fragment does NOT reach. -/
theorem cohesionPointsToPieces_crossModality : cohesionFlat ≠ cohesionShape :=
  fun pathsEqual => cohesionShape_ne_flat pathsEqual.symm

/-! ## The modality-internal laws ACT on the cross-modality hom (populated, non-inert) -/

/-- ★ **A flat-comonad-law detour collapses back onto the transform.**  Pre-composing the transform with the flat
left-counit composite `(ε^♭ ▷ flat) ∘ δ^♭` (which is `≈ id_flat`) yields a cell convertible BACK to the transform:
`((ε^♭ ▷ flat) ∘ δ^♭) ⊟ ptp ≈ ptp`.  So the flat comonad laws genuinely act on the `flat ⇒ shape` hom (it is
populated and non-inert) — yet this does NOT decide whether the hom is THIN; it only shows the modality-internal
structure reaching into it. -/
theorem cohesionPtp_flatCounitLawDetour :
    CohesionSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp cohesionFlatLeftCounitCell cohesionPointsToPiecesCell)
      cohesionPointsToPiecesCell :=
  CohesionSaturatedTwoCellConv.trans
    (CohesionSaturatedTwoCellConv.vcompCongrLeft cohesionPointsToPiecesCell
      CohesionSaturatedTwoCellConv.flatLeftCounit)
    (cohesionConvOfStep (TwoCellStep.vcompIdLeft cohesionPointsToPiecesCell))

/-- ★ **A shape-monad-law detour collapses back onto the transform (dually).**  Post-composing the transform with
the shape left-unit composite `μ^ʃ ∘ (η^ʃ ▷ shape)` (which is `≈ id_shape`) yields a cell convertible back to the
transform: `ptp ⊟ (μ^ʃ ∘ (η^ʃ ▷ shape)) ≈ ptp`.  The shape monad laws also act on the `flat ⇒ shape` hom. -/
theorem cohesionPtp_shapeUnitLawDetour :
    CohesionSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp cohesionPointsToPiecesCell cohesionShapeLeftUnitCell)
      cohesionPointsToPiecesCell :=
  CohesionSaturatedTwoCellConv.trans
    (CohesionSaturatedTwoCellConv.vcompCongrRight cohesionPointsToPiecesCell
      CohesionSaturatedTwoCellConv.shapeLeftUnit)
    (cohesionConvOfStep (TwoCellStep.vcompIdRight cohesionPointsToPiecesCell))

/-! ## Honesty markers -/

/-- ★ **ESTABLISHED — the points-to-pieces transform is exhibited.**  The cross-modality comparison
`cohesionPointsToPiecesCell : flat ⇒ shape` (`vcomp flatCounit shapeUnit`, the walker shadow of the Tier0
`piecesHavePoints`) is a genuine `size 3` composite between the DISTINCT 1-cells `flat` and `shape`
(`cohesionPointsToPieces_crossModality`), and the modality-internal laws act on its hom (the flat-comonad and
shape-monad detours collapse back onto it, `cohesionPtp_flatCounitLawDetour` / `cohesionPtp_shapeUnitLawDetour`).
`= true`. -/
def fxCohesion_hasPointsToPiecesTransform : Bool := true

/-- **Honesty marker — the exact NON-THIN residual (literature-faithful, NOT forced).**  Whether the cross-modality
hom `flat ⇒ shape` is THIN — i.e. whether the points-to-pieces transform is the UNIQUE 2-cell there up to
convertibility, hence whether the FULL cohesion walker is locally posetal — is NOT established.  The three
idempotence collapses identify only modality-INTERNAL power-tower faces, never a cross-modality comparison; and
semantically (nLab *points-to-pieces transform*) the transform is model-dependently non-invertible (an equivalence
only in INFINITESIMAL cohesion / under Aufhebung `♯∅ ≃ ∅`), so the presentation does not force cross-modality
thinness.  This is the exact residual toward the full-walker decision, epistemically the same status as the walking
adjoint triple's open `fxString_hasAdjointTripleCompleteness` (its Δ-like homs already non-thin).  Not forced.
`= false`. -/
def fxCohesion_hasCrossModalityThinness : Bool := false

end FX1Poly.Polygraph
