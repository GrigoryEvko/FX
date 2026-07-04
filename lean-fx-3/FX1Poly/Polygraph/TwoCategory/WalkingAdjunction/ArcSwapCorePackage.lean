import FX1Poly.Polygraph.Computad.AdjunctionSeed
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

/-- ★ **The package feeds the BARE-SPINE peel**: any swap-core package yields equal extracts
after a common `rest` continuation — the per-swap step of the peel induction, which walks the
trace-equivalence chain directly on atom lists (no `runArcCell` wrapper).  The post-rest
event-length pins follow from the core pins because the common `rest` adds the same
`cupAtomCount` / `capAtomCount` to both sides. -/
theorem extractArc_eq_rest_of_swapCorePackage {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (redexCore reductCore : ArcWireState)
    (package : ArcSwapCorePackage bottomCount redexCore reductCore)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    extractArc bottomCount (processArcSpine redexCore rest)
      = extractArc bottomCount (processArcSpine reductCore rest) := by
  have restSim : ArcPartitionSim package.sigma (processArcSpine redexCore rest)
      (processArcSpine reductCore rest) :=
    arcPartitionSim_processArcSpine package.sigma package.sigmaFixesZero rest
      redexCore reductCore package.fixesAbove package.coreSim
  have cupPin : (processArcSpine redexCore rest).cupEventNodes.length
      = (processArcSpine reductCore rest).cupEventNodes.length := by
    rw [processArcSpine_cupEventNodes_length rest redexCore,
      processArcSpine_cupEventNodes_length rest reductCore,
      package.cupLengthsAgree]
  have capPin : (processArcSpine redexCore rest).capEventNodes.length
      = (processArcSpine reductCore rest).capEventNodes.length := by
    rw [processArcSpine_capEventNodes_length rest redexCore,
      processArcSpine_capEventNodes_length rest reductCore,
      package.capLengthsAgree]
  exact extractArc_eq_of_arcPartitionSim bottomCount package.sigma package.sigmaFixesZero
    package.fixesBoundary (processArcSpine redexCore rest) (processArcSpine reductCore rest)
    restSim cupPin capPin

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

/-- The whiskered window position through a LENGTH-TWO generator boundary:
`|leftAcc ; window ; inert| = |inert| + 2 + |leftAcc|` — the packages' high-window spelling. -/
theorem composeWindowPosition_ofTwo {graph : ModeGraph}
    {startMode windowStartMode windowEndMode finishMode : graph.Mode}
    (leftAcc : ModalityPath graph startMode windowStartMode)
    (windowPath : ModalityPath graph windowStartMode windowEndMode)
    (inertPath : ModalityPath graph windowEndMode finishMode)
    (windowTwo : windowPath.length = 2) :
    (composePath (composePath leftAcc windowPath) inertPath).length
      = inertPath.length + 2 + leftAcc.length := by
  rw [composePath_length (composePath leftAcc windowPath) inertPath,
    composePath_length leftAcc windowPath, windowTwo,
    Nat.add_comm (leftAcc.length + 2) inertPath.length,
    ← Nat.add_assoc inertPath.length leftAcc.length 2,
    Nat.add_right_comm inertPath.length leftAcc.length 2]

/-- The whiskered window position through a LENGTH-ZERO generator boundary:
`|leftAcc ; window ; inert| = |inert| + |leftAcc|` — the packages' low-window spelling. -/
theorem composeWindowPosition_ofZero {graph : ModeGraph}
    {startMode windowStartMode windowEndMode finishMode : graph.Mode}
    (leftAcc : ModalityPath graph startMode windowStartMode)
    (windowPath : ModalityPath graph windowStartMode windowEndMode)
    (inertPath : ModalityPath graph windowEndMode finishMode)
    (windowZero : windowPath.length = 0) :
    (composePath (composePath leftAcc windowPath) inertPath).length
      = inertPath.length + leftAcc.length := by
  rw [composePath_length (composePath leftAcc windowPath) inertPath,
    composePath_length leftAcc windowPath, windowZero, Nat.add_zero leftAcc.length,
    Nat.add_comm leftAcc.length inertPath.length]

/-- ★ **THE ATOM-LEVEL DISPATCHER.**  At the walking adjunction, the two-step runs of a
`SpineAtomSwap`-shaped adjacent pair (source order and swapped order, exactly the constructor's
whisker spellings) form a swap-core package, WHICHEVER of the four cup/cap combinations the two
generators are.  Casing on the two generators reduces both `stepArcAtom` runs to the concrete
cup/cap towers, the whiskered window positions re-spell through `composeWindowPosition_ofTwo` /
`_ofZero` into the packages' `gap`/`positionLow` conventions with `gap := inertPath.length` and
`positionLow := leftAcc.length`, and the single uniform `windowsFit` bound specializes to each
combo's window-fit hypothesis. -/
def arcSwapCorePackage_of_adjunctionSwap
    {overallSource overallTarget : adjunctionGraph.Mode}
    {swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode : adjunctionGraph.Mode}
    {oneCellFMid oneCellFHigh : ModalityPath adjunctionGraph swapSourceMode swapMiddleLeft}
    {oneCellGLow oneCellGMid : ModalityPath adjunctionGraph swapMiddleRight swapTargetMode}
    (generatorLeft : adjunctionModeSignature.twoCell oneCellFMid oneCellFHigh)
    (generatorRight : adjunctionModeSignature.twoCell oneCellGLow oneCellGMid)
    (leftAcc : ModalityPath adjunctionGraph overallSource swapSourceMode)
    (inertPath : ModalityPath adjunctionGraph swapMiddleLeft swapMiddleRight)
    (rightAcc : ModalityPath adjunctionGraph swapTargetMode overallTarget)
    (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh)
    (bottomCount : Nat) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (windowsFit : leftAcc.length + oneCellFMid.length + inertPath.length + oneCellGLow.length
      ≤ state.openWires.length) :
    ArcSwapCorePackage bottomCount
      (stepArcAtom
        (stepArcAtom state
          (⟨_, _, leftAcc, _, _, generatorLeft,
            composePath (composePath inertPath oneCellGLow) rightAcc⟩ :
            SpineAtom adjunctionModeSignature overallSource overallTarget))
        (⟨_, _, composePath (composePath leftAcc oneCellFHigh) inertPath, _, _,
          generatorRight, rightAcc⟩ :
          SpineAtom adjunctionModeSignature overallSource overallTarget))
      (stepArcAtom
        (stepArcAtom state
          (⟨_, _, composePath (composePath leftAcc oneCellFMid) inertPath, _, _,
            generatorRight, rightAcc⟩ :
            SpineAtom adjunctionModeSignature overallSource overallTarget))
        (⟨_, _, leftAcc, _, _, generatorLeft,
          composePath (composePath inertPath oneCellGMid) rightAcc⟩ :
          SpineAtom adjunctionModeSignature overallSource overallTarget)) := by
  cases generatorLeft with
  | unit =>
      cases generatorRight with
      | unit =>
          have reducedFit : leftAcc.length + inertPath.length ≤ state.openWires.length :=
            windowsFit
          rw [Nat.add_comm leftAcc.length inertPath.length] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCupArc (stepCupArc state leftAcc.length)
              (composePath (composePath leftAcc adjunctionLeftThenRight) inertPath).length)
            (stepCupArc (stepCupArc state
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
                inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofTwo leftAcc adjunctionLeftThenRight inertPath rfl,
            composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) inertPath rfl]
          exact arcSwapCorePackage_cupCup state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | counit =>
          have reducedFit : leftAcc.length + inertPath.length + 2
              ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm leftAcc.length inertPath.length] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCapArc (stepCupArc state leftAcc.length)
              (composePath (composePath leftAcc adjunctionLeftThenRight) inertPath).length)
            (stepCupArc (stepCapArc state
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
                inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofTwo leftAcc adjunctionLeftThenRight inertPath rfl,
            composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) inertPath rfl]
          exact arcSwapCorePackage_cupCap state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
  | counit =>
      cases generatorRight with
      | unit =>
          have reducedFit : leftAcc.length + 2 + inertPath.length
              ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm (leftAcc.length + 2) inertPath.length,
            ← Nat.add_assoc inertPath.length leftAcc.length 2] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCupArc (stepCapArc state leftAcc.length)
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
                inertPath).length)
            (stepCapArc (stepCupArc state
              (composePath (composePath leftAcc adjunctionRightThenLeft) inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) inertPath rfl,
            composeWindowPosition_ofTwo leftAcc adjunctionRightThenLeft inertPath rfl]
          exact arcSwapCorePackage_capCup state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | counit =>
          have reducedFit : leftAcc.length + 2 + inertPath.length + 2
              ≤ state.openWires.length := windowsFit
          show ArcSwapCorePackage bottomCount
            (stepCapArc (stepCapArc state leftAcc.length)
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
                inertPath).length)
            (stepCapArc (stepCapArc state
              (composePath (composePath leftAcc adjunctionRightThenLeft) inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) inertPath rfl,
            composeWindowPosition_ofTwo leftAcc adjunctionRightThenLeft inertPath rfl]
          exact arcSwapCorePackage_capCap state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length
            (Nat.le_trans (Nat.le_trans
              (Nat.le_add_right (leftAcc.length + 2) inertPath.length)
              (Nat.le_add_right (leftAcc.length + 2 + inertPath.length) 2)) reducedFit)

/-- **Honesty marker — all four two-step swap combos are PEEL-READY.**
`ArcSwapCorePackage` bundles exactly the per-seed inputs of the suffix-peel consumer, and all
four cup/cap combos build it: cup-cup / cup-cap / cap-cup through the renaming bridge
(`arcPartitionSim_of_arcStepSimCount` over their shipped `ArcStepSimCount` cores), cap-cap
through the native `capCapSwap_arcPartitionSim` partition core.
`extractArc_eq_full_of_swapCorePackage` turns any package into equal full-run extracts after a
common continuation, and `extractArc_eq_rest_of_swapCorePackage` does the same for a bare
`rest` spine (the per-swap step the peel induction consumes directly).  The ATOM-LEVEL
dispatcher is ALSO built: `arcSwapCorePackage_of_adjunctionSwap` packages the two-step runs of
a `SpineAtomSwap`-shaped adjacent pair (the constructor's exact whisker spellings) by casing on
the two adjunction generators, under ONE uniform window bound
(`|leftAcc| + |generatorLeft.dom| + |inert| + |generatorRight.dom| <= |openWires|`).
What this marker does NOT claim: the peel induction over bubbling swaps (consuming
`AtomicTraceEquiv` — its chainedness transfer is shipped in `AtomicSwapBoundary`, but the
induction threading the state invariants and the window bound is not) and the ARC-4
reconstruction flip — those are the remaining rungs. -/
def fxMode_hasArcSwapCorePackage : Bool := true

end FX1Poly.Polygraph
