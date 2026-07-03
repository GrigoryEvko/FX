import FX1Poly.Polygraph.TwoCategory.TwoCategoryCore
import FX1Poly.Tier0.Mode.Mode

/-! # mode-1 — the free-1-category / FXModeTheory round-trip over the mode quiver

`mode-1` takes the `mode-0` polygraph signature (`ModeSignature`) and builds the categorical CORE of the mode
theory: the FREE 1-CATEGORY on the mode quiver (packaged as a `RawCategory`, joining the shared categorical
substrate every PolyCell axis plugs into), the free 2-category over it (as a locally-discrete strict 2-category),
and the §3.13 `ModeTheory` / `RigidModeTheory` round-trip target.

The GENERIC strict-2-category core this builds on — the `RawTwoCategory` interface, the
`locallyDiscreteTwoCategory` realizing instance, and the rigidity notion (`RawTwoCategory.IsRigid`,
`rigidTwoCellDecEq`, `locallyDiscreteTwoCategory_isRigid`) — lives in
`FX1Poly.Polygraph.TwoCategory.TwoCategoryCore`; the GENERIC computad carrier this specialises — the quiver, the
free 1-cells with their category laws (`composePath_assoc`, `composePath_identityPath_right`), the generator
embedding (`singletonModalityPath`), and decidable 1-cell equality (`modalityPathDecEq`) — lives in
`FX1Poly.Polygraph.Computad.Signature`.  This file is the mode-axis specialisation packaging that carrier as a
`RawCategory` / §3.13 `ModeTheory`.

## What is built here, and what is deferred

  * ★ **`freeModeCategory`** — the free 1-category on a `ModeGraph` as a genuine `RawCategory` (objects = modes,
    morphisms = modality paths, identity = empty path, composition = concatenation, the three laws PROVED in the
    carrier).  This is where the mode axis JOINS the shared `RawCategory` substrate (the categorical substrate
    all axes plug into); the morphisms ARE the modality paths definitionally (the 1-cell round-trip).
  * **`freeModeTwoCategory`** — the free 1-category exhibited as a (locally discrete) strict 2-category, with the
    1-cell round-trip `(freeModeTwoCategory graph).base = freeModeCategory graph` definitional.
  * the `ModeTheory` / `freeModeTheory` / `RigidModeTheory` / `freeRigidModeTheory` round-trip targets, using the
    carrier's `modalityPathDecEq` for the §3.13 `oneCellEqDecidable`.

DEFERRED (recorded by `= false` markers):
  * the FREE 2-CELL MODEL over the signature's GENERATING 2-cells (`ModeSignature.twoCell`) — a free-2-cell
    term inductive embedding the generators with vertical/horizontal composition + the whisker-functoriality
    coherence, then decidable 2-cell equality — `hasFreeTwoCellGeneratorModel = false` (`mode-3`).  What ships
    here is the 1-categorical core + the locally-discrete 2-category (identity 2-cells only).
  * the §3.13 mode-theory STRUCTURE CLASS — the rigid / `SProp` (proof-irrelevant) 2-cell restriction IS now
    shipped (`RawTwoCategory.IsRigid`, `rigidTwoCellDecEq`, `RigidModeTheory`, `freeRigidModeTheory`); only the
    concrete `FXModeAtom` realization of the named `fxModeTheory` remains deferred (`mode-2`).

Zero external dependencies beyond the `RawCategory` / 2-category substrate + the computad carrier.  Raw Lean 4 +
Init.
-/

namespace FX1Poly.Tier0
open FX1Poly.Polygraph

/-! ## The free 1-category on the mode quiver -/

/-- ★ The **free 1-category** on a mode quiver, as a genuine `RawCategory`: objects are modes, morphisms are
modality paths, identity is the empty path, composition is concatenation, and the three category laws are the
carrier's proofs.  This is the mode axis joining the shared categorical substrate. -/
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

/-! ## The free 2-category on the mode quiver -/

/-- ★ The free 1-category on a mode quiver, exhibited as a (locally discrete) strict 2-category. -/
def freeModeTwoCategory (graph : ModeGraph) : RawTwoCategory :=
  locallyDiscreteTwoCategory (freeModeCategory graph)

/-- Round-trip: the free 2-category's base IS the free 1-category, definitionally. -/
theorem freeModeTwoCategory_base (graph : ModeGraph) :
    (freeModeTwoCategory graph).base = freeModeCategory graph :=
  rfl

/-! ## The §3.13 mode theory + the free construction -/

/-- A **mode theory** in the §3.13 sense: a strict 2-category together with DECIDABLE equality of its 1-cells
(the rigidity that makes modality equality checkable — `fxModeTheory`'s `oneCellEqDecidable`). -/
structure ModeTheory where
  /-- The strict 2-category of modes / modalities / transformations. -/
  twoCategory : RawTwoCategory
  /-- 1-cell (modality) equality is decidable. -/
  oneCellEqDecidable {objectA objectB : twoCategory.base.Object}
    (oneCellF oneCellG : twoCategory.base.Morphism objectA objectB) : Decidable (oneCellF = oneCellG)

/-- ★ The **free mode theory** on a mode quiver with decidable generators: the free 2-category plus decidable
1-cell equality (`modalityPathDecEq`).  A genuine, non-degenerate §3.13 mode theory for ANY decidable quiver —
the `FXModeTheory` round-trip target, realized. -/
def freeModeTheory (graph : ModeGraph)
    (modeDecEq : DecidableEq graph.Mode)
    (modalityDecEq : (sourceMode targetMode : graph.Mode) → DecidableEq (graph.Modality sourceMode targetMode)) :
    ModeTheory where
  twoCategory := freeModeTwoCategory graph
  oneCellEqDecidable := fun oneCellF oneCellG => modalityPathDecEq modeDecEq modalityDecEq oneCellF oneCellG

/-- Round-trip: the free mode theory's 2-category IS the free 2-category, definitionally. -/
theorem freeModeTheory_twoCategory (graph : ModeGraph)
    (modeDecEq : DecidableEq graph.Mode)
    (modalityDecEq : (sourceMode targetMode : graph.Mode) → DecidableEq (graph.Modality sourceMode targetMode)) :
    (freeModeTheory graph modeDecEq modalityDecEq).twoCategory = freeModeTwoCategory graph :=
  rfl

/-! ## The rigid / SProp mode theory (§3.13) -/

/-- The free mode 2-category is rigid (a corollary: every locally discrete 2-category is). -/
theorem freeModeTwoCategory_isRigid (graph : ModeGraph) : (freeModeTwoCategory graph).IsRigid :=
  locallyDiscreteTwoCategory_isRigid (freeModeCategory graph)

/-- A **rigid mode theory**: a §3.13 mode theory whose 2-cells are additionally proof-irrelevant.  The structure
class where BOTH 1-cell equality (`oneCellEqDecidable`) and 2-cell equality (rigidity) are decidable — the
fully-checkable mode theory that the `SProp` 2-cell restriction yields. -/
structure RigidModeTheory extends ModeTheory where
  /-- The 2-cells are proof-irrelevant (the rigidity / `SProp` restriction). -/
  isRigid : twoCategory.IsRigid

/-- ★ The free mode theory on a decidable quiver is rigid — both 1-cell and 2-cell equality are decidable. -/
def freeRigidModeTheory (graph : ModeGraph)
    (modeDecEq : DecidableEq graph.Mode)
    (modalityDecEq : (sourceMode targetMode : graph.Mode) → DecidableEq (graph.Modality sourceMode targetMode)) :
    RigidModeTheory where
  toModeTheory := freeModeTheory graph modeDecEq modalityDecEq
  isRigid := freeModeTwoCategory_isRigid graph

/-! ## Honesty markers -/

/-- **Honesty marker.**  The FREE 2-CELL MODEL over a signature's GENERATING 2-cells (`ModeSignature.twoCell`)
— a free-2-cell term inductive embedding the generators with vertical/horizontal composition + the
whisker-functoriality coherence, then decidable 2-cell equality — is `mode-3`, deferred.  What ships here is the
1-categorical core + the locally-discrete 2-category (identity 2-cells only).  `= false`. -/
def fxMode_hasFreeTwoCellGeneratorModel : Bool := false

/-- **Honesty marker.**  The §3.13 mode-theory rigid / `SProp` proof-irrelevant 2-cell restriction IS shipped
(`RawTwoCategory.IsRigid` + `rigidTwoCellDecEq` + `RigidModeTheory` + the free witness).  What remains deferred
is the concrete `FXModeAtom` realization of the specific `fxModeTheory` (the named atoms), `mode-2`.  `= false`. -/
def fxMode_hasModeTheoryStructureClass : Bool := false

end FX1Poly.Tier0
