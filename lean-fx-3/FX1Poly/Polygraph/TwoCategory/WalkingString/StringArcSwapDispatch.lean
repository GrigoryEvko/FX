import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapCorePackage

/-! # WalkingString/StringArcSwapDispatch — the atom-level swap-core dispatcher (FC-3 item 1, the producer)

The peel's per-swap step needs, at the walking ADJOINT TRIPLE, a swap-core package for the two-step runs of a
`SpineAtomSwap`-shaped adjacent pair.  The four generic two-step builders (`arcSwapCorePackage_cupCup` /
`_cupCap` / `_capCup` / `_capCap`) are ALREADY signature-generic — they operate on a bare `ArcWireState` and the
concrete `stepCupArc` / `stepCapArc` towers, colour-blind.  The only signature-keyed piece is the DISPATCHER that
cases on the two generators, reduces each `stepArcAtom` run to the concrete cup/cap tower (via the arity-driven
`stepArcAtom`, so a string cup reduces exactly as an adjunction unit), re-spells the whiskered window positions
through `composeWindowPosition_ofTwo` / `_ofZero`, and routes to the builder its arity picks.

At the walking ADJUNCTION this dispatcher (`arcSwapCorePackage_of_adjunctionSwap`) has 2×2 = 4 arms.  The adjoint
triple has FOUR generators, so it grows to 4×4 = 16 arms — but each arm is EXACTLY one of the four adjunction arms
with the concrete string boundary word substituted (`stringFG`/`stringGH` for cup cods, `stringGF`/`stringHG` for
cap doms, each length 2 by `rfl`; the empty word for the opposite side).  The window re-spelling reads only the
LEFT generator's dom/cod LENGTHS (`_ofTwo` at length 2, `_ofZero` at length 0), the RIGHT generator only selects
the builder's cup/cap suffix — so the 16 arms collapse to the four arity templates, colour-blind throughout.  NO
length-rigidity is used: the window positions are pure `composePath` length bookkeeping, valid at any signature.

Raw Lean 4 + Init; each arm is a `show` reducing `stepArcAtom` to the cup/cap tower, a `composeWindowPosition`
re-spelling, and a generic builder application, exactly mirroring the adjunction dispatcher.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **THE ATOM-LEVEL DISPATCHER (four generators).**  At the walking adjoint triple, the two-step runs of a
`SpineAtomSwap`-shaped adjacent pair (source order and swapped order, the constructor's whisker spellings) form a
swap-core package, WHICHEVER of the sixteen generator combinations the two generators are.  Casing on the two
generators reduces both `stepArcAtom` runs to the concrete cup/cap towers, the whiskered window positions re-spell
through `composeWindowPosition_ofTwo` / `_ofZero` into the packages' `gap`/`positionLow` conventions (with
`gap := inertPath.length`, `positionLow := leftAcc.length`), and the single uniform `windowsFit` bound specializes
to each combo's window-fit hypothesis.  The direct four-generator analog of `arcSwapCorePackage_of_adjunctionSwap`;
every window step reads only cup/cap arity, never colour. -/
def stringArcSwapCorePackage_of_stringSwap
    {overallSource overallTarget : adjointTripleGraph.Mode}
    {swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode : adjointTripleGraph.Mode}
    {oneCellFMid oneCellFHigh : ModalityPath adjointTripleGraph swapSourceMode swapMiddleLeft}
    {oneCellGLow oneCellGMid : ModalityPath adjointTripleGraph swapMiddleRight swapTargetMode}
    (generatorLeft : adjointTripleModeSignature.twoCell oneCellFMid oneCellFHigh)
    (generatorRight : adjointTripleModeSignature.twoCell oneCellGLow oneCellGMid)
    (leftAcc : ModalityPath adjointTripleGraph overallSource swapSourceMode)
    (inertPath : ModalityPath adjointTripleGraph swapMiddleLeft swapMiddleRight)
    (rightAcc : ModalityPath adjointTripleGraph swapTargetMode overallTarget)
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
            SpineAtom adjointTripleModeSignature overallSource overallTarget))
        (⟨_, _, composePath (composePath leftAcc oneCellFHigh) inertPath, _, _,
          generatorRight, rightAcc⟩ :
          SpineAtom adjointTripleModeSignature overallSource overallTarget))
      (stepArcAtom
        (stepArcAtom state
          (⟨_, _, composePath (composePath leftAcc oneCellFMid) inertPath, _, _,
            generatorRight, rightAcc⟩ :
            SpineAtom adjointTripleModeSignature overallSource overallTarget))
        (⟨_, _, leftAcc, _, _, generatorLeft,
          composePath (composePath inertPath oneCellGMid) rightAcc⟩ :
          SpineAtom adjointTripleModeSignature overallSource overallTarget)) := by
  cases generatorLeft with
  | unitLower =>
      cases generatorRight with
      | unitLower =>
          have reducedFit : leftAcc.length + inertPath.length ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm leftAcc.length inertPath.length] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCupArc (stepCupArc state leftAcc.length)
              (composePath (composePath leftAcc stringFG) inertPath).length)
            (stepCupArc (stepCupArc state
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
                inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofTwo leftAcc stringFG inertPath rfl,
            composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) inertPath rfl]
          exact arcSwapCorePackage_cupCup state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | unitUpper =>
          have reducedFit : leftAcc.length + inertPath.length ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm leftAcc.length inertPath.length] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCupArc (stepCupArc state leftAcc.length)
              (composePath (composePath leftAcc stringFG) inertPath).length)
            (stepCupArc (stepCupArc state
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
                inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofTwo leftAcc stringFG inertPath rfl,
            composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) inertPath rfl]
          exact arcSwapCorePackage_cupCup state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | counitLower =>
          have reducedFit : leftAcc.length + inertPath.length + 2 ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm leftAcc.length inertPath.length] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCapArc (stepCupArc state leftAcc.length)
              (composePath (composePath leftAcc stringFG) inertPath).length)
            (stepCupArc (stepCapArc state
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
                inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofTwo leftAcc stringFG inertPath rfl,
            composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) inertPath rfl]
          exact arcSwapCorePackage_cupCap state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | counitUpper =>
          have reducedFit : leftAcc.length + inertPath.length + 2 ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm leftAcc.length inertPath.length] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCapArc (stepCupArc state leftAcc.length)
              (composePath (composePath leftAcc stringFG) inertPath).length)
            (stepCupArc (stepCapArc state
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
                inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofTwo leftAcc stringFG inertPath rfl,
            composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) inertPath rfl]
          exact arcSwapCorePackage_cupCap state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
  | unitUpper =>
      cases generatorRight with
      | unitLower =>
          have reducedFit : leftAcc.length + inertPath.length ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm leftAcc.length inertPath.length] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCupArc (stepCupArc state leftAcc.length)
              (composePath (composePath leftAcc stringGH) inertPath).length)
            (stepCupArc (stepCupArc state
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))
                inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofTwo leftAcc stringGH inertPath rfl,
            composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) inertPath rfl]
          exact arcSwapCorePackage_cupCup state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | unitUpper =>
          have reducedFit : leftAcc.length + inertPath.length ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm leftAcc.length inertPath.length] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCupArc (stepCupArc state leftAcc.length)
              (composePath (composePath leftAcc stringGH) inertPath).length)
            (stepCupArc (stepCupArc state
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))
                inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofTwo leftAcc stringGH inertPath rfl,
            composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) inertPath rfl]
          exact arcSwapCorePackage_cupCup state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | counitLower =>
          have reducedFit : leftAcc.length + inertPath.length + 2 ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm leftAcc.length inertPath.length] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCapArc (stepCupArc state leftAcc.length)
              (composePath (composePath leftAcc stringGH) inertPath).length)
            (stepCupArc (stepCapArc state
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))
                inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofTwo leftAcc stringGH inertPath rfl,
            composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) inertPath rfl]
          exact arcSwapCorePackage_cupCap state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | counitUpper =>
          have reducedFit : leftAcc.length + inertPath.length + 2 ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm leftAcc.length inertPath.length] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCapArc (stepCupArc state leftAcc.length)
              (composePath (composePath leftAcc stringGH) inertPath).length)
            (stepCupArc (stepCapArc state
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))
                inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofTwo leftAcc stringGH inertPath rfl,
            composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) inertPath rfl]
          exact arcSwapCorePackage_cupCap state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
  | counitLower =>
      cases generatorRight with
      | unitLower =>
          have reducedFit : leftAcc.length + 2 + inertPath.length ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm (leftAcc.length + 2) inertPath.length,
            ← Nat.add_assoc inertPath.length leftAcc.length 2] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCupArc (stepCapArc state leftAcc.length)
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))
                inertPath).length)
            (stepCapArc (stepCupArc state
              (composePath (composePath leftAcc stringGF) inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) inertPath rfl,
            composeWindowPosition_ofTwo leftAcc stringGF inertPath rfl]
          exact arcSwapCorePackage_capCup state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | unitUpper =>
          have reducedFit : leftAcc.length + 2 + inertPath.length ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm (leftAcc.length + 2) inertPath.length,
            ← Nat.add_assoc inertPath.length leftAcc.length 2] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCupArc (stepCapArc state leftAcc.length)
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))
                inertPath).length)
            (stepCapArc (stepCupArc state
              (composePath (composePath leftAcc stringGF) inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) inertPath rfl,
            composeWindowPosition_ofTwo leftAcc stringGF inertPath rfl]
          exact arcSwapCorePackage_capCup state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | counitLower =>
          have reducedFit : leftAcc.length + 2 + inertPath.length + 2 ≤ state.openWires.length := windowsFit
          show ArcSwapCorePackage bottomCount
            (stepCapArc (stepCapArc state leftAcc.length)
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))
                inertPath).length)
            (stepCapArc (stepCapArc state
              (composePath (composePath leftAcc stringGF) inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) inertPath rfl,
            composeWindowPosition_ofTwo leftAcc stringGF inertPath rfl]
          exact arcSwapCorePackage_capCap state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length
            (Nat.le_trans (Nat.le_trans
              (Nat.le_add_right (leftAcc.length + 2) inertPath.length)
              (Nat.le_add_right (leftAcc.length + 2 + inertPath.length) 2)) reducedFit)
      | counitUpper =>
          have reducedFit : leftAcc.length + 2 + inertPath.length + 2 ≤ state.openWires.length := windowsFit
          show ArcSwapCorePackage bottomCount
            (stepCapArc (stepCapArc state leftAcc.length)
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))
                inertPath).length)
            (stepCapArc (stepCapArc state
              (composePath (composePath leftAcc stringGF) inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) inertPath rfl,
            composeWindowPosition_ofTwo leftAcc stringGF inertPath rfl]
          exact arcSwapCorePackage_capCap state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length
            (Nat.le_trans (Nat.le_trans
              (Nat.le_add_right (leftAcc.length + 2) inertPath.length)
              (Nat.le_add_right (leftAcc.length + 2 + inertPath.length) 2)) reducedFit)
  | counitUpper =>
      cases generatorRight with
      | unitLower =>
          have reducedFit : leftAcc.length + 2 + inertPath.length ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm (leftAcc.length + 2) inertPath.length,
            ← Nat.add_assoc inertPath.length leftAcc.length 2] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCupArc (stepCapArc state leftAcc.length)
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
                inertPath).length)
            (stepCapArc (stepCupArc state
              (composePath (composePath leftAcc stringHG) inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) inertPath rfl,
            composeWindowPosition_ofTwo leftAcc stringHG inertPath rfl]
          exact arcSwapCorePackage_capCup state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | unitUpper =>
          have reducedFit : leftAcc.length + 2 + inertPath.length ≤ state.openWires.length := windowsFit
          rw [Nat.add_comm (leftAcc.length + 2) inertPath.length,
            ← Nat.add_assoc inertPath.length leftAcc.length 2] at reducedFit
          show ArcSwapCorePackage bottomCount
            (stepCupArc (stepCapArc state leftAcc.length)
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
                inertPath).length)
            (stepCapArc (stepCupArc state
              (composePath (composePath leftAcc stringHG) inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) inertPath rfl,
            composeWindowPosition_ofTwo leftAcc stringHG inertPath rfl]
          exact arcSwapCorePackage_capCup state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length reducedFit
      | counitLower =>
          have reducedFit : leftAcc.length + 2 + inertPath.length + 2 ≤ state.openWires.length := windowsFit
          show ArcSwapCorePackage bottomCount
            (stepCapArc (stepCapArc state leftAcc.length)
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
                inertPath).length)
            (stepCapArc (stepCapArc state
              (composePath (composePath leftAcc stringHG) inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) inertPath rfl,
            composeWindowPosition_ofTwo leftAcc stringHG inertPath rfl]
          exact arcSwapCorePackage_capCap state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length
            (Nat.le_trans (Nat.le_trans
              (Nat.le_add_right (leftAcc.length + 2) inertPath.length)
              (Nat.le_add_right (leftAcc.length + 2 + inertPath.length) 2)) reducedFit)
      | counitUpper =>
          have reducedFit : leftAcc.length + 2 + inertPath.length + 2 ≤ state.openWires.length := windowsFit
          show ArcSwapCorePackage bottomCount
            (stepCapArc (stepCapArc state leftAcc.length)
              (composePath (composePath leftAcc
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
                inertPath).length)
            (stepCapArc (stepCapArc state
              (composePath (composePath leftAcc stringHG) inertPath).length)
              leftAcc.length)
          rw [composeWindowPosition_ofZero leftAcc
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) inertPath rfl,
            composeWindowPosition_ofTwo leftAcc stringHG inertPath rfl]
          exact arcSwapCorePackage_capCap state fresh forest nextFreshPos bottomCount
            boundaryBelowFresh inertPath.length leftAcc.length
            (Nat.le_trans (Nat.le_trans
              (Nat.le_add_right (leftAcc.length + 2) inertPath.length)
              (Nat.le_add_right (leftAcc.length + 2 + inertPath.length) 2)) reducedFit)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the four-generator atom-level swap-core dispatcher is machine-checked (FC-3 item 1 producer).**
`stringArcSwapCorePackage_of_stringSwap` packages the two-step runs of any `SpineAtomSwap`-shaped adjacent pair at
the walking adjoint triple by casing on the two generators (16 arms), reducing each `stepArcAtom` to its concrete
cup/cap tower and routing to the four generic builders (`arcSwapCorePackage_cupCup` / `_cupCap` / `_capCup` /
`_capCap`) under ONE uniform window bound.  Each arm is exactly one of the four adjunction dispatcher arms with the
concrete string boundary word substituted (`stringFG`/`stringGH`/`stringGF`/`stringHG`, each length 2 by `rfl`); the
window re-spelling reads only cup/cap arity (colour-blind), so no length-rigidity is used.  This is the item-1
PRODUCER the peel consumes per swap.  `= true`. -/
def fxString_hasArcSwapDispatch : Bool := true

end FX1Poly.Polygraph
