import FX1Poly.Polygraph.Category.RawCategory

/-! # The strict 2-category core (generic, over an arbitrary `RawCategory`)

The generic, context-free strict-2-category core: the `RawTwoCategory` interface (a base `RawCategory` of 0/1-cells
+ a `TwoCell` family + vertical identity/composition + whiskering + horizontal composition + interchange), the
`locallyDiscreteTwoCategory` realizing instance over ANY `RawCategory` (2-cells are equalities of 1-cells, every
law by proof irrelevance), and the rigidity notion (`RawTwoCategory.IsRigid` + the decidable-2-cell-equality
consequence `rigidTwoCellDecEq` + the witness `locallyDiscreteTwoCategory_isRigid`).

This is pure category theory over an ARBITRARY `RawCategory` — nothing here mentions the mode quiver, modality
paths, or any PolyCell axis.  The mode-axis specialisation — the free 1-category / free 2-category on a `ModeGraph`,
the §3.13 `ModeTheory` / `RigidModeTheory` and their free constructions — lives in
`FX1Poly.Axis.Mode.TwoCategoryCore` and builds on this core.

Zero external dependencies beyond the `RawCategory` substrate.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Polygraph

/-! ## The strict 2-category interface -/

/-- A **strict 2-category** (the mode-theory shape): a base `RawCategory` of 0- and 1-cells, a `TwoCell` family
between PARALLEL 1-cells, vertical identity/composition forming a category in each hom, left/right whiskering of
2-cells by 1-cells, horizontal composition, and the interchange law.  A mode theory is such a structure;
`mode-1` ships the interface and a realizing instance, `mode-3` the free model over generating 2-cells. -/
structure RawTwoCategory where
  /-- The base category of 0- and 1-cells. -/
  base : RawCategory
  /-- 2-cells between a parallel pair of 1-cells. -/
  TwoCell {objectA objectB : base.Object} :
    base.Morphism objectA objectB → base.Morphism objectA objectB → Type
  /-- The identity 2-cell on a 1-cell. -/
  idTwo {objectA objectB : base.Object} (oneCell : base.Morphism objectA objectB) : TwoCell oneCell oneCell
  /-- Vertical composition of 2-cells. -/
  vcomp {objectA objectB : base.Object} {oneCellF oneCellG oneCellH : base.Morphism objectA objectB}
    (cellAlpha : TwoCell oneCellF oneCellG) (cellBeta : TwoCell oneCellG oneCellH) : TwoCell oneCellF oneCellH
  /-- Vertical composition is associative. -/
  vcompAssoc {objectA objectB : base.Object}
    {oneCellF oneCellG oneCellH oneCellK : base.Morphism objectA objectB}
    (cellAlpha : TwoCell oneCellF oneCellG) (cellBeta : TwoCell oneCellG oneCellH)
    (cellGamma : TwoCell oneCellH oneCellK) :
    vcomp (vcomp cellAlpha cellBeta) cellGamma = vcomp cellAlpha (vcomp cellBeta cellGamma)
  /-- The identity 2-cell is a left unit for vertical composition. -/
  vcompIdLeft {objectA objectB : base.Object} {oneCellF oneCellG : base.Morphism objectA objectB}
    (cellAlpha : TwoCell oneCellF oneCellG) : vcomp (idTwo oneCellF) cellAlpha = cellAlpha
  /-- The identity 2-cell is a right unit for vertical composition. -/
  vcompIdRight {objectA objectB : base.Object} {oneCellF oneCellG : base.Morphism objectA objectB}
    (cellAlpha : TwoCell oneCellF oneCellG) : vcomp cellAlpha (idTwo oneCellG) = cellAlpha
  /-- Left whiskering: precompose a 2-cell with a 1-cell. -/
  whiskerLeft {objectA objectB objectC : base.Object} (oneCellF : base.Morphism objectA objectB)
    {oneCellG oneCellH : base.Morphism objectB objectC} (cellBeta : TwoCell oneCellG oneCellH) :
    TwoCell (base.compose oneCellF oneCellG) (base.compose oneCellF oneCellH)
  /-- Right whiskering: postcompose a 2-cell with a 1-cell. -/
  whiskerRight {objectA objectB objectC : base.Object} {oneCellF oneCellG : base.Morphism objectA objectB}
    (oneCellH : base.Morphism objectB objectC) (cellAlpha : TwoCell oneCellF oneCellG) :
    TwoCell (base.compose oneCellF oneCellH) (base.compose oneCellG oneCellH)
  /-- Left whiskering preserves the identity 2-cell (whiskering is functorial — the unit law). -/
  whiskerLeft_id {objectA objectB objectC : base.Object} (oneCellF : base.Morphism objectA objectB)
    (oneCellG : base.Morphism objectB objectC) :
    whiskerLeft oneCellF (idTwo oneCellG) = idTwo (base.compose oneCellF oneCellG)
  /-- Right whiskering preserves the identity 2-cell (whiskering is functorial — the unit law). -/
  whiskerRight_id {objectA objectB objectC : base.Object} (oneCellF : base.Morphism objectA objectB)
    (oneCellG : base.Morphism objectB objectC) :
    whiskerRight oneCellG (idTwo oneCellF) = idTwo (base.compose oneCellF oneCellG)
  /-- Left whiskering distributes over vertical composition (whiskering is functorial). -/
  whiskerLeft_vcomp {objectA objectB objectC : base.Object} (oneCellF : base.Morphism objectA objectB)
    {oneCellG oneCellH oneCellK : base.Morphism objectB objectC}
    (cellBeta : TwoCell oneCellG oneCellH) (cellGamma : TwoCell oneCellH oneCellK) :
    whiskerLeft oneCellF (vcomp cellBeta cellGamma)
      = vcomp (whiskerLeft oneCellF cellBeta) (whiskerLeft oneCellF cellGamma)
  /-- Right whiskering distributes over vertical composition (whiskering is functorial). -/
  whiskerRight_vcomp {objectA objectB objectC : base.Object}
    {oneCellF oneCellG oneCellH : base.Morphism objectA objectB} (oneCellK : base.Morphism objectB objectC)
    (cellAlpha : TwoCell oneCellF oneCellG) (cellBeta : TwoCell oneCellG oneCellH) :
    whiskerRight oneCellK (vcomp cellAlpha cellBeta)
      = vcomp (whiskerRight oneCellK cellAlpha) (whiskerRight oneCellK cellBeta)
  /-- Horizontal composition of 2-cells. -/
  horizontalCompose {objectA objectB objectC : base.Object}
    {oneCellFDom oneCellFCod : base.Morphism objectA objectB}
    {oneCellGDom oneCellGCod : base.Morphism objectB objectC}
    (cellAlpha : TwoCell oneCellFDom oneCellFCod) (cellBeta : TwoCell oneCellGDom oneCellGCod) :
    TwoCell (base.compose oneCellFDom oneCellGDom) (base.compose oneCellFCod oneCellGCod)
  /-- The interchange law relating horizontal and vertical composition. -/
  interchange {objectA objectB objectC : base.Object}
    {oneCellFLow oneCellFMid oneCellFHigh : base.Morphism objectA objectB}
    {oneCellGLow oneCellGMid oneCellGHigh : base.Morphism objectB objectC}
    (cellAlpha : TwoCell oneCellFLow oneCellFMid) (cellAlphaUpper : TwoCell oneCellFMid oneCellFHigh)
    (cellBeta : TwoCell oneCellGLow oneCellGMid) (cellBetaUpper : TwoCell oneCellGMid oneCellGHigh) :
    horizontalCompose (vcomp cellAlpha cellAlphaUpper) (vcomp cellBeta cellBetaUpper)
      = vcomp (horizontalCompose cellAlpha cellBeta) (horizontalCompose cellAlphaUpper cellBetaUpper)

/-- The **locally discrete 2-category** over any `RawCategory`: 2-cells are EQUALITIES of parallel 1-cells.
Every 2-cell law holds by definitional proof irrelevance of the `Prop` 2-cells (each `rfl`), so the interface
is genuinely realizable without `funext`.  The genuine (non-identity) 2-cells generated by a signature's
`twoCell` are the `mode-3` enrichment on top of this. -/
def locallyDiscreteTwoCategory (category : RawCategory) : RawTwoCategory where
  base := category
  TwoCell := fun oneCellF oneCellG => PLift (oneCellF = oneCellG)
  idTwo := fun _ => PLift.up rfl
  vcomp := fun cellAlpha cellBeta => PLift.up (cellAlpha.down.trans cellBeta.down)
  vcompAssoc := fun _ _ _ => rfl
  vcompIdLeft := fun cellAlpha => by cases cellAlpha; rfl
  vcompIdRight := fun _ => rfl
  whiskerLeft := fun {_ _ _} oneCellF {_ _} cellBeta =>
    PLift.up (congrArg (fun oneCell => category.compose oneCellF oneCell) cellBeta.down)
  whiskerRight := fun {_ _ _} {_ _} oneCellH cellAlpha =>
    PLift.up (congrArg (fun oneCell => category.compose oneCell oneCellH) cellAlpha.down)
  whiskerLeft_id := by intros; rfl
  whiskerRight_id := by intros; rfl
  whiskerLeft_vcomp := by intros; rfl
  whiskerRight_vcomp := by intros; rfl
  horizontalCompose := fun {_ _ _ oneCellFDom _ _ oneCellGCod} cellAlpha cellBeta =>
    PLift.up ((congrArg (fun oneCell => category.compose oneCellFDom oneCell) cellBeta.down).trans
      (congrArg (fun oneCell => category.compose oneCell oneCellGCod) cellAlpha.down))
  interchange := fun _ _ _ _ => rfl

/-! ## The rigid / SProp 2-cell restriction (§3.13) -/

/-- A strict 2-category is **rigid** (the §3.13 / Gratzer-MTT `SProp` restriction) when its 2-cells are
PROOF-IRRELEVANT: any two parallel 2-cells are equal.  This is exactly what placing the `TwoCell` family in
`SProp` would give definitionally; since the interface here is `Type`-valued, rigidity is the propositional
subsingleton condition.  Rigidity is the mode-theory structure class that makes 2-cell equality decidable. -/
def RawTwoCategory.IsRigid (twoCategory : RawTwoCategory) : Prop :=
  ∀ {objectA objectB : twoCategory.base.Object} {oneCellF oneCellG : twoCategory.base.Morphism objectA objectB}
    (cellAlpha cellBeta : twoCategory.TwoCell oneCellF oneCellG), cellAlpha = cellBeta

/-- ★ A **rigid** 2-category has DECIDABLE 2-cell equality, trivially: any two parallel 2-cells are equal by
rigidity, so the decision is always `isTrue`.  This is why the §3.13 rigid mode theory sidesteps the 2-cell word
problem (`mode-3`'s hard core) — the cost being that genuinely-distinct parallel 2-cells collapse. -/
def RawTwoCategory.rigidTwoCellDecEq {twoCategory : RawTwoCategory} (isRigid : twoCategory.IsRigid)
    {objectA objectB : twoCategory.base.Object} {oneCellF oneCellG : twoCategory.base.Morphism objectA objectB}
    (cellAlpha cellBeta : twoCategory.TwoCell oneCellF oneCellG) : Decidable (cellAlpha = cellBeta) :=
  .isTrue (isRigid cellAlpha cellBeta)

/-- The **locally discrete** 2-category is rigid: its 2-cells are `PLift (f = g)` of a `Prop`, hence
proof-irrelevant (definitional in Lean — the `PLift.up` of two proofs of one `Prop` are defeq).  The concrete
witness that the rigid structure class is inhabited. -/
theorem locallyDiscreteTwoCategory_isRigid (category : RawCategory) :
    (locallyDiscreteTwoCategory category).IsRigid := by
  intro _ _ _ _ cellAlpha cellBeta
  cases cellAlpha
  cases cellBeta
  rfl

end FX1Poly.Polygraph
