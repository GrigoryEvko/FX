import FX1Poly.Tier0.Context.RepresentableMapCategory
import FX1Poly.Tier0.Mode.Mode

/-! # mode-1 — the strict 2-category core + the free-1-category / FXModeTheory round-trip

`mode-1` takes the `mode-0` polygraph signature (`ModeSignature`) and builds the categorical CORE of the mode
theory: the FREE 1-CATEGORY on the mode quiver (packaged as a `RawCategory`, joining the shared categorical
substrate every PolyCell axis plugs into), the STRICT 2-CATEGORY interface (`RawTwoCategory`), and a genuine
instance witnessing the interface is realizable and lawful.

## What is built here, and what is deferred

  * **the path-category laws** — `composePath_assoc` and `composePath_identityPath_right` (the left identity was
    already definitional in `mode-0`), by structural induction on a path, zero-axiom.
  * ★ **`freeModeCategory`** — the free 1-category on a `ModeGraph` as a genuine `RawCategory` (objects = modes,
    morphisms = modality paths, identity = empty path, composition = concatenation, the three laws PROVED).
    This is where the mode axis JOINS the shared `RawCategory` substrate (the categorical substrate all axes
    plug into); the morphisms ARE the modality paths definitionally (the 1-cell round-trip).
  * **`RawTwoCategory`** — the strict 2-category interface: a base `RawCategory` (0/1-cells) + a `TwoCell`
    family between parallel 1-cells + vertical identity/composition with its category laws + left/right
    whiskering + horizontal composition + the interchange law.
  * **`locallyDiscreteTwoCategory`** — a genuine `RawTwoCategory` instance over ANY `RawCategory`: the locally
    discrete 2-category whose 2-cells are EQUALITIES of 1-cells (`PLift (oneCellF = oneCellG)`).  Every 2-cell
    law holds by definitional proof irrelevance of the `Prop` 2-cells, so each is `rfl` — no `funext`.  This
    realizes the interface and exhibits the free 1-category as a (locally discrete) strict 2-category
    (`freeModeTwoCategory`), with the 1-cell round-trip `(freeModeTwoCategory graph).base = freeModeCategory
    graph` definitional.

DEFERRED (recorded by `= false` markers):
  * the FREE 2-CELL MODEL over the signature's GENERATING 2-cells (`ModeSignature.twoCell`) — a free-2-cell
    term inductive embedding the generators with vertical/horizontal composition + the whisker-functoriality
    coherence, then decidable 2-cell equality — `hasFreeTwoCellGeneratorModel = false` (`mode-3`).  What ships
    here is the 1-categorical core + the locally-discrete 2-category (identity 2-cells only).
  * the §3.13 mode-theory STRUCTURE CLASS — the rigid / `SProp` (proof-irrelevant) 2-cell restriction and the
    `FXModeAtom` realization of `fxModeTheory` — `hasModeTheoryStructureClass = false` (`mode-2`).

Zero external dependencies beyond the `RawCategory` substrate.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The free 1-category on the mode quiver -/

/-- Path composition is associative — by structural induction on the first path (the recursive call threads
the `∀`-quantified tail paths, kept in the conclusion so the motive stays general). -/
theorem composePath_assoc {graph : ModeGraph} {sourceMode middleMode : graph.Mode}
    (first : ModalityPath graph sourceMode middleMode) :
    ∀ {nextMode lastMode : graph.Mode}
      (second : ModalityPath graph middleMode nextMode) (third : ModalityPath graph nextMode lastMode),
      composePath (composePath first second) third = composePath first (composePath second third) := by
  induction first with
  | nil _ => intro _ _ second third; rfl
  | cons modality rest ih => intro _ _ second third; exact congrArg (ModalityPath.cons modality) (ih second third)

/-- The empty path is a right identity for composition (the left identity is definitional, `mode-0`). -/
theorem composePath_identityPath_right {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (path : ModalityPath graph sourceMode targetMode) :
    composePath path (identityPath targetMode) = path := by
  induction path with
  | nil _ => rfl
  | cons modality rest ih => exact congrArg (ModalityPath.cons modality) ih

/-- ★ The **free 1-category** on a mode quiver, as a genuine `RawCategory`: objects are modes, morphisms are
modality paths, identity is the empty path, composition is concatenation, and the three category laws are the
proofs above.  This is the mode axis joining the shared categorical substrate. -/
def freeModeCategory (graph : ModeGraph) : RawCategory where
  Object := graph.Mode
  Morphism := ModalityPath graph
  identity := identityPath
  compose := composePath
  composeAssoc := fun first second third => composePath_assoc first second third
  identityLeft := composePath_identityPath_left
  identityRight := composePath_identityPath_right

/-- The 1-cell round-trip: the free category's morphisms ARE the modality paths, definitionally. -/
theorem freeModeCategory_morphism_eq_modalityPath (graph : ModeGraph) (sourceMode targetMode : graph.Mode) :
    (freeModeCategory graph).Morphism sourceMode targetMode = ModalityPath graph sourceMode targetMode :=
  rfl

/-- A generating modality embeds as the length-1 1-cell (the single-step path). -/
def singletonModalityPath {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (modality : graph.Modality sourceMode targetMode) : ModalityPath graph sourceMode targetMode :=
  ModalityPath.cons modality (ModalityPath.nil targetMode)

/-- The generator embedding has length 1 (a freeness smoke: generators are exactly the atomic 1-cells). -/
theorem singletonModalityPath_length {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (modality : graph.Modality sourceMode targetMode) : (singletonModalityPath modality).length = 1 :=
  rfl

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
  vcompIdRight := fun cellAlpha => by cases cellAlpha; rfl
  whiskerLeft := fun {_ _ _} oneCellF {_ _} cellBeta =>
    PLift.up (congrArg (fun oneCell => category.compose oneCellF oneCell) cellBeta.down)
  whiskerRight := fun {_ _ _} {_ _} oneCellH cellAlpha =>
    PLift.up (congrArg (fun oneCell => category.compose oneCell oneCellH) cellAlpha.down)
  horizontalCompose := fun {_ _ _ oneCellFDom _ _ oneCellGCod} cellAlpha cellBeta =>
    PLift.up ((congrArg (fun oneCell => category.compose oneCellFDom oneCell) cellBeta.down).trans
      (congrArg (fun oneCell => category.compose oneCell oneCellGCod) cellAlpha.down))
  interchange := fun _ _ _ _ => rfl

/-- ★ The free 1-category on a mode quiver, exhibited as a (locally discrete) strict 2-category. -/
def freeModeTwoCategory (graph : ModeGraph) : RawTwoCategory :=
  locallyDiscreteTwoCategory (freeModeCategory graph)

/-- Round-trip: the free 2-category's base IS the free 1-category, definitionally. -/
theorem freeModeTwoCategory_base (graph : ModeGraph) :
    (freeModeTwoCategory graph).base = freeModeCategory graph :=
  rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The FREE 2-CELL MODEL over a signature's GENERATING 2-cells (`ModeSignature.twoCell`)
— a free-2-cell term inductive embedding the generators with vertical/horizontal composition + the
whisker-functoriality coherence, then decidable 2-cell equality — is `mode-3`, deferred.  What ships here is the
1-categorical core + the locally-discrete 2-category (identity 2-cells only).  `= false`. -/
def fxMode_hasFreeTwoCellGeneratorModel : Bool := false

/-- **Honesty marker.**  The §3.13 mode-theory STRUCTURE CLASS — the rigid / `SProp` proof-irrelevant 2-cell
restriction and the `FXModeAtom` realization of `fxModeTheory` — is `mode-2`, deferred.  `= false`. -/
def fxMode_hasModeTheoryStructureClass : Bool := false

end FX1Poly.Tier0
