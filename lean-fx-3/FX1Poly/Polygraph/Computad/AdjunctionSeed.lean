import FX1Poly.Polygraph.Computad.Signature

/-! # Polygraph/Computad/AdjunctionSeed — the canonical non-degenerate 2-computad: the walking-adjunction seed

The canonical NON-DEGENERATE witness for the 2-computad carrier — the two-mode adjunction / cohesion seed: two
distinct 0-cells, a 1-cell generator each way, and unit / counit 2-cell GENERATORS between non-trivial parallel
free 1-cells.  It exercises every dimension of the `ModeSignature` data model, and it is the presented signature
the walking-adjunction free-2-cell rewriting tower is instantiated at.

Generic presentation data (no mode-theory dependence), so it lives in the signature-free `Polygraph/` library.
The triangle laws relating unit and counit are the GENERATORS only here; orienting them as 3-cells and proving
convergence is the free-2-cell tower's job.

Zero external dependencies beyond the computad signature.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Polygraph

/-! ## The canonical non-degenerate witness: the two-mode adjunction / cohesion seed -/

/-- The two modes of the adjunction seed. -/
inductive AdjunctionMode where
  /-- The source mode. -/
  | base
  /-- The target mode. -/
  | tip

/-- The modality generators of the adjunction seed: one in each direction. -/
inductive AdjunctionModality : AdjunctionMode → AdjunctionMode → Type where
  /-- The left modality `base ⟶ tip`. -/
  | left : AdjunctionModality AdjunctionMode.base AdjunctionMode.tip
  /-- The right modality `tip ⟶ base`. -/
  | right : AdjunctionModality AdjunctionMode.tip AdjunctionMode.base

/-- The adjunction-seed quiver: two modes, a modality each way. -/
def adjunctionGraph : ModeGraph where
  Mode := AdjunctionMode
  Modality := AdjunctionModality

/-- The composite 1-cell `base ⟶ tip ⟶ base` (left then right) — a non-trivial endo-path at `base`. -/
def adjunctionLeftThenRight : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.base :=
  ModalityPath.cons AdjunctionModality.left
    (ModalityPath.cons AdjunctionModality.right
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))

/-- The composite 1-cell `tip ⟶ base ⟶ tip` (right then left) — a non-trivial endo-path at `tip`. -/
def adjunctionRightThenLeft : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.tip :=
  ModalityPath.cons AdjunctionModality.right
    (ModalityPath.cons AdjunctionModality.left
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))

/-- The generating 2-cells of the adjunction seed — the unit and counit, between non-trivial parallel paths.
These are the GENERATORS only; the triangle laws relating them are deferred (`mode-3` / `mode-4`). -/
inductive AdjunctionTwoCell :
    {sourceMode targetMode : AdjunctionMode} →
    ModalityPath adjunctionGraph sourceMode targetMode →
    ModalityPath adjunctionGraph sourceMode targetMode → Type where
  /-- The unit `id_base ⟹ (left then right)`. -/
  | unit : AdjunctionTwoCell (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
      adjunctionLeftThenRight
  /-- The counit `(right then left) ⟹ id_tip`. -/
  | counit : AdjunctionTwoCell adjunctionRightThenLeft
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)

/-- ★ The **adjunction / cohesion mode signature** — the canonical NON-DEGENERATE witness: two distinct modes,
a modality each way, and unit/counit 2-cell generators between non-trivial parallel paths.  It exercises every
dimension of the data model (modes, typed modalities, composite paths, 2-cells between distinct parallel
paths). -/
def adjunctionModeSignature : ModeSignature where
  graph := adjunctionGraph
  twoCell := fun firstPath secondPath => AdjunctionTwoCell firstPath secondPath

end FX1Poly.Polygraph
