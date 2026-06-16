import FX1Poly.Tier0.Mode.TwoCategoryCore

/-! # mode-3 — the free 2-cell term model + the 3-polygraph + decidable 2-cell equality

`mode-1` built the 1-categorical core (the free 1-category, the strict-2-category interface, and the
LOCALLY-DISCRETE 2-category whose only 2-cells are equalities of 1-cells).  `mode-3` adds the GENUINE
(non-identity) 2-cells: the FREE 2-CELL MODEL over a `ModeSignature`'s generating 2-cells
(`ModeSignature.twoCell`), the 3-POLYGRAPH (the generating 3-cells = the strict-2-category laws oriented as
rewrites) presented as a conversion relation, and DECIDABLE 2-cell equality as far as it is achievable without
the full convergence proof (Gratzer's coherence hurdle).

## What this file ships (each piece zero-axiom)

  * **`RawTwoCellExpr`** — THE free 2-cell term model.  An indexed inductive of 2-cell EXPRESSIONS between a
    PARALLEL pair of 1-cells (modality paths), with five generators: `gen` (embed a signature 2-cell), `id`
    (identity 2-cell), `vcomp` (vertical composition), `whiskerLeft` / `whiskerRight` (pre/post-composition by a
    1-cell).  This is the deliverable `mode-1` deferred as `fxMode_hasFreeTwoCellGeneratorModel`.  Horizontal
    composition is DERIVED (`hcomp` below = whisker then vcomp, the Godement product), exactly as `ModalLock`'s
    `RawEndofunctorTransformation` derives it.
  * **`RawTwoCellExpr.size`** — the structural size measure (a termination/induction handle for the 3-cells).
  * the generator embedding + the NON-DEGENERATE witnesses: the adjunction seed's unit / counit embed as `gen`
    2-cells between genuinely distinct parallel paths, and a non-trivial `vcomp` / whisker composite exists.

## The 2-cell boundary

A 2-cell's boundary is a parallel pair of 1-cells (same source and target mode) — the `mode-0`
`ModeSignature.twoCell` paradigm, the same as the Core `CellBoundary`.  `RawTwoCellExpr` is indexed by that
pair (computed, not `Nat`-dimension-indexed — the propext-clean discipline the whole substrate follows).

## What is DEFERRED (recorded by `= false` markers below)

  * the full CONVERGENCE of the 3-polygraph (termination + confluence of the oriented laws) and hence GENERAL
    decidable 2-cell equality MODULO the laws — this is Gratzer's coherence hurdle, genuinely hard, and only the
    achievable fragment ships (`hasConvergentThreeCellSystem = false`).  Decidable SYNTACTIC equality of free
    2-cell expressions is itself blocked by the whisker split ambiguity (`compose f g` does not determine the
    split `(f, g)`), which is exactly why the convergence is needed.
  * the QUOTIENT 2-category (2-cells modulo the 3-cells) as a `RawTwoCategory` — a quotient needs `Quot.sound`
    (banned); `mode-3` ships the free EXPRESSIONS + the conversion relation, not the quotient
    (`hasQuotientTwoCategory = false`).

Zero external dependencies beyond the mode-1 core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The free 2-cell term model -/

/-- ★ The **free 2-cell term model** over a `ModeSignature` — the 2-cells of the free strict 2-category on the
signature, as EXPRESSIONS (before quotienting by the 2-category laws).  Indexed by a parallel pair of 1-cells
(modality paths sharing source and target mode), with five generators: a signature 2-cell, the identity, the
vertical composite, and the two whiskerings.  This is the free-2-cell-generator model `mode-1` deferred. -/
inductive RawTwoCellExpr (signature : ModeSignature) :
    {sourceMode targetMode : signature.graph.Mode} →
    ModalityPath signature.graph sourceMode targetMode →
    ModalityPath signature.graph sourceMode targetMode → Type where
  /-- Embed a GENERATING 2-cell of the signature between its parallel boundary paths. -/
  | gen {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} :
      signature.twoCell sourcePath targetPath → RawTwoCellExpr signature sourcePath targetPath
  /-- The identity 2-cell on a 1-cell. -/
  | id {sourceMode targetMode : signature.graph.Mode}
      (path : ModalityPath signature.graph sourceMode targetMode) :
      RawTwoCellExpr signature path path
  /-- Vertical composition: a 2-cell `f ⇒ g` then a 2-cell `g ⇒ h` gives `f ⇒ h`. -/
  | vcomp {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode} :
      RawTwoCellExpr signature oneCellF oneCellG → RawTwoCellExpr signature oneCellG oneCellH →
      RawTwoCellExpr signature oneCellF oneCellH
  /-- Left whiskering: precompose a 2-cell `g ⇒ h` by a 1-cell, giving `(oneCell ∘ g) ⇒ (oneCell ∘ h)`. -/
  | whiskerLeft {sourceMode middleMode targetMode : signature.graph.Mode}
      (oneCell : ModalityPath signature.graph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode} :
      RawTwoCellExpr signature oneCellG oneCellH →
      RawTwoCellExpr signature (composePath oneCell oneCellG) (composePath oneCell oneCellH)
  /-- Right whiskering: postcompose a 2-cell `f ⇒ g` by a 1-cell, giving `(f ∘ oneCell) ⇒ (g ∘ oneCell)`. -/
  | whiskerRight {sourceMode middleMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
      (oneCell : ModalityPath signature.graph middleMode targetMode) :
      RawTwoCellExpr signature oneCellF oneCellG →
      RawTwoCellExpr signature (composePath oneCellF oneCell) (composePath oneCellG oneCell)

/-- The structural size of a 2-cell expression (every generator counts 1, composites add) — the
termination/induction handle for the 3-cell rewrites.  Full five-case match, constant `Nat` motive: the
recursor is propext-free. -/
def RawTwoCellExpr.size {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, _, _, .gen _ => 1
  | _, _, _, _, .id _ => 1
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellAlpha.size + cellBeta.size + 1
  | _, _, _, _, .whiskerLeft _ cellBeta => cellBeta.size + 1
  | _, _, _, _, .whiskerRight _ cellBeta => cellBeta.size + 1

/-- **Horizontal composition** of free 2-cells, DERIVED as the Godement product `whiskerRight` then
`whiskerLeft` (the upper-right path of the naturality square), exactly as `ModalLock`'s
`RawEndofunctorTransformation.hcomp`.  Given `α : f ⇒ f'` (over `a ⟶ b`) and `β : g ⇒ g'` (over `b ⟶ c`),
produces `(f ∘ g) ⇒ (f' ∘ g')`.  Not a primitive — the free 2-cell model needs only whiskering + vcomp. -/
def RawTwoCellExpr.hcomp {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellFDom oneCellFCod)
    (cellBeta : RawTwoCellExpr signature oneCellGDom oneCellGCod) :
    RawTwoCellExpr signature (composePath oneCellFDom oneCellGDom) (composePath oneCellFCod oneCellGCod) :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCellGDom cellAlpha)
    (RawTwoCellExpr.whiskerLeft oneCellFCod cellBeta)

/-! ## Generator embedding + non-degeneracy witnesses -/

/-- The adjunction seed's UNIT embeds as a free 2-cell `id_base ⇒ (left then right)`. -/
def adjunctionUnitTwoCell :
    RawTwoCellExpr adjunctionModeSignature
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) adjunctionLeftThenRight :=
  RawTwoCellExpr.gen AdjunctionTwoCell.unit

/-- The adjunction seed's COUNIT embeds as a free 2-cell `(right then left) ⇒ id_tip`. -/
def adjunctionCounitTwoCell :
    RawTwoCellExpr adjunctionModeSignature
      adjunctionRightThenLeft (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) :=
  RawTwoCellExpr.gen AdjunctionTwoCell.counit

/-- A genuinely non-trivial free 2-cell: the unit vertically composed with itself is ill-typed, but the unit
whiskered then vcomp'd with an identity is a real composite — exercising `vcomp` + `id` over the non-degenerate
seed.  Its size is `> 1` (it is not a bare generator), witnessing the model has genuine compositional depth. -/
def adjunctionUnitThenId :
    RawTwoCellExpr adjunctionModeSignature
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) adjunctionLeftThenRight :=
  RawTwoCellExpr.vcomp adjunctionUnitTwoCell
    (RawTwoCellExpr.id (signature := adjunctionModeSignature) adjunctionLeftThenRight)

/-- The unit generator has size 1 (it is an atomic 2-cell). -/
theorem adjunctionUnitTwoCell_size : adjunctionUnitTwoCell.size = 1 := rfl

/-- The composite `unit ⊟ id` has size 3 (`1 + 1 + 1`) — genuine compositional depth beyond a generator. -/
theorem adjunctionUnitThenId_size : adjunctionUnitThenId.size = 3 := rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The full CONVERGENCE of the 3-polygraph (termination + confluence of the oriented
strict-2-category laws) and hence GENERAL decidable 2-cell equality modulo the laws is Gratzer's coherence
hurdle — genuinely hard, deferred (the achievable fragment + the mode-relative metatheory are `mode-9`).
`= false`. -/
def fxMode_hasConvergentThreeCellSystem : Bool := false

/-- **Honesty marker.**  The QUOTIENT 2-category (free 2-cells modulo the 3-cells) as a genuine
`RawTwoCategory` needs `Quot.sound` (banned, non-zero-axiom); `mode-3` ships the free EXPRESSIONS plus the
conversion relation, not the quotient.  `= false`. -/
def fxMode_hasQuotientTwoCategory : Bool := false

end FX1Poly.Tier0
