import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPartitionSimStep
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPartitionSimulation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshBlockTransposition
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCupSwapSimulation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCapSwapSimulation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapCupSwapSimulation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapCapSwapCore

/-! # WalkingAdjunction/ArcSwapCorePackage — the four two-step swap cores, PEEL-READY

The suffix-peel consumer (`extractArc_eq_full_of_corePartitionSim`) needs, at the swap seed:
a `sigma`, its three fixing facts (zero / boundary / above the core's fresh counter), the core
`ArcPartitionSim`, and the two event-list length pins.  This file bundles exactly those seven
fields into `ArcSwapCorePackage` and builds the bundle for ALL FOUR cup/cap two-step combos:
the three heterogeneous combos ride their shipped `ArcStepSimCount` cores through the
`arcPartitionSim_of_arcStepSimCount` bridge, and the cap-cap combo uses the native
`capCapSwap_arcPartitionSim` partition core (the one the renaming vehicle provably cannot
produce).  Every builder is uniform in the same seed hypotheses: state freshness, forest,
`0 < nextFresh`, a boundary bound, and the combo's window-fit bound.

Orientation convention (inherited from all four cores): the package's `redexCore` is the
LOW-FIRST run, `reductCore` the HIGH-FIRST run.  The mirrored swap's consumer symms the final
extract equality.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The peel-ready swap-core bundle** — exactly the per-seed inputs of
`extractArc_eq_full_of_corePartitionSim`, with the event transposition packaged as data. -/
structure ArcSwapCorePackage (bottomCount : Nat) (redexCore reductCore : ArcWireState) where
  /-- The event renaming between the two run orders. -/
  sigma : Nat → Nat
  /-- The renaming fixes the zero fallback identifier. -/
  sigmaFixesZero : sigma 0 = 0
  /-- The renaming fixes every boundary identifier. -/
  fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier
  /-- The renaming fixes everything the common suffix will allocate. -/
  fixesAbove : ∀ identifier, redexCore.nextFresh ≤ identifier → sigma identifier = identifier
  /-- The two-step core partition simulation. -/
  coreSim : ArcPartitionSim sigma redexCore reductCore
  /-- The cup-event lists have equal length. -/
  cupLengthsAgree : redexCore.cupEventNodes.length = reductCore.cupEventNodes.length
  /-- The cap-event lists have equal length. -/
  capLengthsAgree : redexCore.capEventNodes.length = reductCore.capEventNodes.length

/-- ★ **The package feeds the suffix peel**: any swap-core package yields equal full-run
extracts after the common `suffixCell`-then-`rest` continuation. -/
theorem extractArc_eq_full_of_swapCorePackage {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {cellSource cellTarget : signature.graph.Mode}
    (bottomCount : Nat) (redexCore reductCore : ArcWireState)
    (package : ArcSwapCorePackage bottomCount redexCore reductCore)
    (leftAccCell : ModalityPath signature.graph overallSource cellSource)
    (rightAccCell : ModalityPath signature.graph cellTarget overallTarget)
    {cellDom cellCod : ModalityPath signature.graph cellSource cellTarget}
    (suffixCell : RawTwoCellExpr signature cellDom cellCod)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    extractArc bottomCount
        (processArcSpine (runArcCell redexCore leftAccCell rightAccCell suffixCell) rest)
      = extractArc bottomCount
          (processArcSpine (runArcCell reductCore leftAccCell rightAccCell suffixCell) rest) :=
  extractArc_eq_full_of_corePartitionSim package.sigma package.sigmaFixesZero bottomCount
    package.fixesBoundary redexCore reductCore leftAccCell rightAccCell suffixCell rest
    package.fixesAbove package.coreSim package.cupLengthsAgree package.capLengthsAgree

/-- **CUP x CUP package** — the width-`3`/`3` event transposition over the shipped
`arcStepSimCount_cupCupSwap`, bridged to the partition level. -/
def arcSwapCorePackage_cupCup (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh)
    (bottomCount : Nat) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (gap positionLow : Nat)
    (positionBound : gap + positionLow ≤ state.openWires.length) :
    ArcSwapCorePackage bottomCount
      (stepCupArc (stepCupArc state positionLow) (gap + 2 + positionLow))
      (stepCupArc (stepCupArc state (gap + positionLow)) positionLow) where
  sigma := arcFreshBlockTransposition state.nextFresh 3 3
  sigmaFixesZero := arcFreshBlockTransposition_fixesZero state.nextFresh 3 3 nextFreshPos
  fixesBoundary := fun identifier identifierBelow =>
    arcFreshBlockTransposition_ofBelow state.nextFresh 3 3 identifier
      (Nat.lt_of_lt_of_le identifierBelow boundaryBelowFresh)
  fixesAbove := fun identifier identifierAtLeast =>
    arcFreshBlockTransposition_ofAtOrAbove state.nextFresh 3 3 identifier identifierAtLeast
  coreSim := arcPartitionSim_of_arcStepSimCount
    (arcFreshBlockTransposition state.nextFresh 3 3)
    (fun leftPreimage rightPreimage =>
      arcFreshBlockTransposition_injective state.nextFresh 3 3 leftPreimage rightPreimage)
    (stepCupArc (stepCupArc state positionLow) (gap + 2 + positionLow))
    (stepCupArc (stepCupArc state (gap + positionLow)) positionLow)
    (arcStepSimCount_cupCupSwap state fresh forest gap positionLow positionBound)
  cupLengthsAgree := rfl
  capLengthsAgree := rfl

/-- **CUP x CAP package** — the width-`3`/`1` event transposition over the shipped
`arcStepSimCount_cupCapSwap`. -/
def arcSwapCorePackage_cupCap (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh)
    (bottomCount : Nat) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length) :
    ArcSwapCorePackage bottomCount
      (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow))
      (stepCupArc (stepCapArc state (gap + positionLow)) positionLow) where
  sigma := arcFreshBlockTransposition state.nextFresh 3 1
  sigmaFixesZero := arcFreshBlockTransposition_fixesZero state.nextFresh 3 1 nextFreshPos
  fixesBoundary := fun identifier identifierBelow =>
    arcFreshBlockTransposition_ofBelow state.nextFresh 3 1 identifier
      (Nat.lt_of_lt_of_le identifierBelow boundaryBelowFresh)
  fixesAbove := fun identifier identifierAtLeast =>
    arcFreshBlockTransposition_ofAtOrAbove state.nextFresh 3 1 identifier identifierAtLeast
  coreSim := arcPartitionSim_of_arcStepSimCount
    (arcFreshBlockTransposition state.nextFresh 3 1)
    (fun leftPreimage rightPreimage =>
      arcFreshBlockTransposition_injective state.nextFresh 3 1 leftPreimage rightPreimage)
    (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow))
    (stepCupArc (stepCapArc state (gap + positionLow)) positionLow)
    (arcStepSimCount_cupCapSwap state fresh forest nextFreshPos gap positionLow positionBound)
  cupLengthsAgree := rfl
  capLengthsAgree := rfl

/-- **CAP x CUP package** — the width-`1`/`3` event transposition over the shipped
`arcStepSimCount_capCupSwap`. -/
def arcSwapCorePackage_capCup (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh)
    (bottomCount : Nat) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length) :
    ArcSwapCorePackage bottomCount
      (stepCupArc (stepCapArc state positionLow) (gap + positionLow))
      (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow) where
  sigma := arcFreshBlockTransposition state.nextFresh 1 3
  sigmaFixesZero := arcFreshBlockTransposition_fixesZero state.nextFresh 1 3 nextFreshPos
  fixesBoundary := fun identifier identifierBelow =>
    arcFreshBlockTransposition_ofBelow state.nextFresh 1 3 identifier
      (Nat.lt_of_lt_of_le identifierBelow boundaryBelowFresh)
  fixesAbove := fun identifier identifierAtLeast =>
    arcFreshBlockTransposition_ofAtOrAbove state.nextFresh 1 3 identifier identifierAtLeast
  coreSim := arcPartitionSim_of_arcStepSimCount
    (arcFreshBlockTransposition state.nextFresh 1 3)
    (fun leftPreimage rightPreimage =>
      arcFreshBlockTransposition_injective state.nextFresh 1 3 leftPreimage rightPreimage)
    (stepCupArc (stepCapArc state positionLow) (gap + positionLow))
    (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow)
    (arcStepSimCount_capCupSwap state fresh forest nextFreshPos gap positionLow positionBound)
  cupLengthsAgree := rfl
  capLengthsAgree := rfl

/-- **CAP x CAP package** — the width-`1`/`1` event transposition over the NATIVE partition
core `capCapSwap_arcPartitionSim` (the combo the renaming vehicle provably cannot handle). -/
def arcSwapCorePackage_capCap (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh)
    (bottomCount : Nat) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (gap positionLow : Nat)
    (lowWindowFits : positionLow + 2 ≤ state.openWires.length) :
    ArcSwapCorePackage bottomCount
      (stepCapArc (stepCapArc state positionLow) (gap + positionLow))
      (stepCapArc (stepCapArc state (gap + 2 + positionLow)) positionLow) where
  sigma := arcFreshBlockTransposition state.nextFresh 1 1
  sigmaFixesZero := arcFreshBlockTransposition_fixesZero state.nextFresh 1 1 nextFreshPos
  fixesBoundary := fun identifier identifierBelow =>
    arcFreshBlockTransposition_ofBelow state.nextFresh 1 1 identifier
      (Nat.lt_of_lt_of_le identifierBelow boundaryBelowFresh)
  fixesAbove := fun identifier identifierAtLeast =>
    arcFreshBlockTransposition_ofAtOrAbove state.nextFresh 1 1 identifier identifierAtLeast
  coreSim := capCapSwap_arcPartitionSim state positionLow gap forest fresh lowWindowFits
  cupLengthsAgree := rfl
  capLengthsAgree := rfl

/-- **Honesty marker — all four two-step swap combos are PEEL-READY.**
`ArcSwapCorePackage` bundles exactly the per-seed inputs of the suffix-peel consumer, and all
four cup/cap combos build it: cup-cup / cup-cap / cap-cup through the renaming bridge
(`arcPartitionSim_of_arcStepSimCount` over their shipped `ArcStepSimCount` cores), cap-cap
through the native `capCapSwap_arcPartitionSim` partition core.
`extractArc_eq_full_of_swapCorePackage` turns any package into equal full-run extracts after a
common continuation.  What this marker does NOT claim: the ATOM-LEVEL dispatcher (reading a
realized `SpineAtomSwap` at the walking-adjunction seed, casing on the two generators, and
reconciling the window positions into the packages' `gap`/`positionLow` spellings), the peel
induction over bubbling swaps, and the ARC-4 reconstruction flip — those are the remaining
rungs. -/
def fxMode_hasArcSwapCorePackage : Bool := true

end FX1Poly.Polygraph
