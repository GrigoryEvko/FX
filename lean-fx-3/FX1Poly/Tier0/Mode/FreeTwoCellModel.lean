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

/-! ## The 3-polygraph: the oriented 3-cells + 2-cell conversion

The strict-2-category laws, ORIENTED left-to-right as rewrites, are the GENERATING 3-CELLS of the mode
theory's 3-polygraph: remove identity 2-cells, right-associate vertical composites, and push whiskerings
inward (the interchange normal-form orientation, after Guiraud–Malbos polygraphic rewriting).  `TwoCellStep`
is the one-step rewrite (the generating 3-cells closed under context — `whiskerLeft`/`whiskerRight`/`vcomp`
congruence); `TwoCellConv` is its reflexive-symmetric-transitive closure — 2-cell CONVERTIBILITY, the
equivalence the free strict 2-category quotients by.  Both are `Prop`-valued (defining them is axiom-free). -/

/-- One **3-cell** (oriented rewrite step) between parallel free 2-cells — the generating relations (the
strict-2-category laws oriented toward interchange normal form) closed under congruence so a redex fires in
any sub-position. -/
inductive TwoCellStep (signature : ModeSignature) :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath →
    RawTwoCellExpr signature sourcePath targetPath → Prop where
  /-- Drop a left identity: `id ⊟ α ⟶ α`. -/
  | vcompIdLeft {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG : ModalityPath signature.graph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG) :
      TwoCellStep signature (RawTwoCellExpr.vcomp (RawTwoCellExpr.id oneCellF) cellAlpha) cellAlpha
  /-- Drop a right identity: `α ⊟ id ⟶ α`. -/
  | vcompIdRight {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG : ModalityPath signature.graph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG) :
      TwoCellStep signature (RawTwoCellExpr.vcomp cellAlpha (RawTwoCellExpr.id oneCellG)) cellAlpha
  /-- Right-associate vertical composition: `(α ⊟ β) ⊟ γ ⟶ α ⊟ (β ⊟ γ)`. -/
  | vcompAssoc {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH oneCellK : ModalityPath signature.graph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
      (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
      (cellGamma : RawTwoCellExpr signature oneCellH oneCellK) :
      TwoCellStep signature
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.vcomp cellAlpha cellBeta) cellGamma)
        (RawTwoCellExpr.vcomp cellAlpha (RawTwoCellExpr.vcomp cellBeta cellGamma))
  /-- Whiskering an identity is an identity (left): `oneCell ◁ id ⟶ id`. -/
  | whiskerLeftId {sourceMode middleMode targetMode : signature.graph.Mode}
      (oneCell : ModalityPath signature.graph sourceMode middleMode)
      (path : ModalityPath signature.graph middleMode targetMode) :
      TwoCellStep signature (RawTwoCellExpr.whiskerLeft oneCell (RawTwoCellExpr.id path))
        (RawTwoCellExpr.id (composePath oneCell path))
  /-- Whiskering an identity is an identity (right): `id ▷ oneCell ⟶ id`. -/
  | whiskerRightId {sourceMode middleMode targetMode : signature.graph.Mode}
      (path : ModalityPath signature.graph sourceMode middleMode)
      (oneCell : ModalityPath signature.graph middleMode targetMode) :
      TwoCellStep signature (RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.id path))
        (RawTwoCellExpr.id (composePath path oneCell))
  /-- Left whiskering distributes over vertical composition: `oneCell ◁ (β ⊟ γ) ⟶ (oneCell ◁ β) ⊟ (oneCell ◁ γ)`. -/
  | whiskerLeftVcomp {sourceMode middleMode targetMode : signature.graph.Mode}
      (oneCell : ModalityPath signature.graph sourceMode middleMode)
      {oneCellG oneCellH oneCellK : ModalityPath signature.graph middleMode targetMode}
      (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
      (cellGamma : RawTwoCellExpr signature oneCellH oneCellK) :
      TwoCellStep signature (RawTwoCellExpr.whiskerLeft oneCell (RawTwoCellExpr.vcomp cellBeta cellGamma))
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
          (RawTwoCellExpr.whiskerLeft oneCell cellGamma))
  /-- Right whiskering distributes over vertical composition. -/
  | whiskerRightVcomp {sourceMode middleMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode middleMode}
      (oneCell : ModalityPath signature.graph middleMode targetMode)
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
      (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
      TwoCellStep signature (RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.vcomp cellAlpha cellBeta))
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
          (RawTwoCellExpr.whiskerRight oneCell cellBeta))
  /-- Congruence: a step in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
      TwoCellStep signature cellAlpha cellAlpha' →
      TwoCellStep signature (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence: a step in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} :
      TwoCellStep signature cellBeta cellBeta' →
      TwoCellStep signature (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence: a step under a left whiskering. -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : signature.graph.Mode}
      (oneCell : ModalityPath signature.graph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} :
      TwoCellStep signature cellBeta cellBeta' →
      TwoCellStep signature (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence: a step under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
      (oneCell : ModalityPath signature.graph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG} :
      TwoCellStep signature cellAlpha cellAlpha' →
      TwoCellStep signature (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')

/-- **2-cell convertibility** — the reflexive-symmetric-transitive closure of the 3-cell rewrite `TwoCellStep`.
This is the equivalence the free strict 2-category on the signature quotients its 2-cells by (the quotient
itself needs `Quot.sound`, deferred — see the marker); two free 2-cells are equal AS 2-CELLS of the strict
2-category exactly when they are `TwoCellConv`-related. -/
inductive TwoCellConv (signature : ModeSignature) :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath →
    RawTwoCellExpr signature sourcePath targetPath → Prop where
  /-- A single 3-cell rewrite is a conversion. -/
  | ofStep {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} :
      TwoCellStep signature cellAlpha cellBeta → TwoCellConv signature cellAlpha cellBeta
  /-- Reflexivity. -/
  | refl {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr signature sourcePath targetPath) :
      TwoCellConv signature cellAlpha cellAlpha
  /-- Symmetry. -/
  | symm {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} :
      TwoCellConv signature cellAlpha cellBeta → TwoCellConv signature cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellBeta cellGamma : RawTwoCellExpr signature sourcePath targetPath} :
      TwoCellConv signature cellAlpha cellBeta → TwoCellConv signature cellBeta cellGamma →
      TwoCellConv signature cellAlpha cellGamma

/-- Smoke: the left-unit 3-cell fires on the adjunction seed — `id ⊟ unit` rewrites to `unit`. -/
theorem adjunctionUnit_vcompIdLeft_step :
    TwoCellStep adjunctionModeSignature
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.id (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
        adjunctionUnitTwoCell)
      adjunctionUnitTwoCell :=
  TwoCellStep.vcompIdLeft adjunctionUnitTwoCell

/-- Smoke: hence `id ⊟ unit` is CONVERTIBLE to `unit` (a one-step conversion) — and the non-degenerate
composite `adjunctionUnitThenId` (`unit ⊟ id`) is convertible to `unit` by the right-unit law. -/
theorem adjunctionUnitThenId_conv_unit :
    TwoCellConv adjunctionModeSignature adjunctionUnitThenId adjunctionUnitTwoCell :=
  TwoCellConv.ofStep (TwoCellStep.vcompIdRight adjunctionUnitTwoCell)

/-! ## 3-cell normal forms + the decidability interface

A free 2-cell is in INTERCHANGE NORMAL FORM when no `TwoCellStep` redex pattern occurs anywhere in it: no
vertical composite has an identity factor or a left-nested composite, and no whiskering wraps an identity or a
composite.  `isInterchangeNormal` is the structural recognizer for exactly those patterns.  DECIDABLE 2-cell
equality (the §3.13 / Gratzer property) is then "normalize both, compare" — but the normalization needs the
3-polygraph to be CONVERGENT (terminating + confluent), which is the deferred hurdle (`mode-9`); what ships
here is the recognizer plus the decidability INTERFACE the convergence would inhabit. -/

/-- Whether a free 2-cell's head constructor is the identity (`id`) — a structural one-symbol probe used by the
normal-form recognizer.  Constant `Bool` motive, full five-case: propext-free. -/
def RawTwoCellExpr.isIdentityCell {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Bool
  | _, _, _, _, .id _ => true
  | _, _, _, _, .gen _ => false
  | _, _, _, _, .vcomp _ _ => false
  | _, _, _, _, .whiskerLeft _ _ => false
  | _, _, _, _, .whiskerRight _ _ => false

/-- Whether a free 2-cell's head constructor is a vertical composite (`vcomp`). -/
def RawTwoCellExpr.isVcompCell {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Bool
  | _, _, _, _, .vcomp _ _ => true
  | _, _, _, _, .gen _ => false
  | _, _, _, _, .id _ => false
  | _, _, _, _, .whiskerLeft _ _ => false
  | _, _, _, _, .whiskerRight _ _ => false

/-- ★ The **3-cell normal-form recognizer**: `true` exactly when NO `TwoCellStep` redex occurs in the
expression.  A vertical composite is normal when neither factor is an identity (no `vcompId*`), the left factor
is not itself a composite (no `vcompAssoc`), and both factors are normal; a whiskering is normal when its body
is neither an identity nor a composite (no `whisker{Id,Vcomp}`) and is normal.  Generators and identities are
atomic normal forms.  Structural recursion, constant `Bool` motive — propext-free. -/
def RawTwoCellExpr.isInterchangeNormal {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Bool
  | _, _, _, _, .gen _ => true
  | _, _, _, _, .id _ => true
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      !cellAlpha.isIdentityCell && !cellBeta.isIdentityCell && !cellAlpha.isVcompCell
        && cellAlpha.isInterchangeNormal && cellBeta.isInterchangeNormal
  | _, _, _, _, .whiskerLeft _ cellBeta =>
      !cellBeta.isIdentityCell && !cellBeta.isVcompCell && cellBeta.isInterchangeNormal
  | _, _, _, _, .whiskerRight _ cellBeta =>
      !cellBeta.isIdentityCell && !cellBeta.isVcompCell && cellBeta.isInterchangeNormal

/-- Smoke: a bare generator (the adjunction unit) IS an interchange normal form. -/
theorem adjunctionUnitTwoCell_isInterchangeNormal :
    adjunctionUnitTwoCell.isInterchangeNormal = true := rfl

/-- Smoke: the redex `unit ⊟ id` is NOT normal (its right factor is an identity — a `vcompIdRight` redex), so
the recognizer correctly rejects it.  Its convertibility to the normal `unit` is
`adjunctionUnitThenId_conv_unit`. -/
theorem adjunctionUnitThenId_not_isInterchangeNormal :
    adjunctionUnitThenId.isInterchangeNormal = false := rfl

/-- The **decidable-2-cell-equality interface** (the §3.13 / Gratzer property a presented mode theory must
expose): 2-cell CONVERTIBILITY (`TwoCellConv`) is decidable on every parallel pair of free 2-cells.  This is
what `mode-9`'s convergence proof would inhabit (normalize both via the 3-polygraph, compare normal forms);
`mode-3` ships the interface and the recognizer, not the procedure (the convergence is deferred). -/
def DecidableTwoCellConvFor (signature : ModeSignature) : Type :=
  {sourceMode targetMode : signature.graph.Mode} →
  {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
  (cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath) →
  Decidable (TwoCellConv signature cellAlpha cellBeta)

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
