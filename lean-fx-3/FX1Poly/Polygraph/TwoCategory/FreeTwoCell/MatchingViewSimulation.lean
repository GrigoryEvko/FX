import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingViewStability
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentGodement
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline

/-! # mode-3 — the connectivity-view simulation (bundle + per-atom dispatch + spine fold)

Two runs related only through the CONNECTIVITY VIEW — equal open-wire counts, equal loop
counts, and agreeing boundary same-component relations on in-range index pairs — stay related
through every boundary-disciplined spine.  This file bundles the relation
(`MatchingConnectivityViewSim`), dispatches one disciplined atom onto the shipped cap/cup
transports (`matchingConnectivityViewSim_stepAtom` — the arity reads off
`AtomHasCupOrCapArity`, the window bound reads off the tracked `domBoundaryLength`), and folds
it over a whole disciplined spine (`matchingConnectivityViewSim_processSpine`, threading
`MatchingSwapStateConditions` on both states via `matchingSwapStateConditions_stepAtom` and
the length tracking via `stepAtom_openWires_tracksBoundary` — the same invariant-threading
shape as `traceInvariant_of_boundaryDiscipline`).

Consumers: the `MatchingSaturatedCongruence` fields need exactly this — the premise
`matchingOf cellAlpha = matchingOf cellAlpha'` reconstructs a view sim at the shared state,
and the fold carries it through the composite's remaining spine.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The connectivity-view simulation relation**: two states agree on everything the
extract reads through the boundary — open-wire count, loop count, and the same-component
relation at every in-range boundary-index pair. -/
structure MatchingConnectivityViewSim (bottomCount : Nat) (stateT stateS : WireState) : Prop
    where
  /-- The open-wire counts agree. -/
  lengthEq : stateT.openWires.length = stateS.openWires.length
  /-- The loop counts agree. -/
  loopsEq : stateT.loops = stateS.loops
  /-- The connectivity views agree at every in-range boundary-index pair. -/
  viewAgrees : ∀ firstIndex secondIndex,
    firstIndex < bottomCount + stateS.openWires.length →
    secondIndex < bottomCount + stateS.openWires.length →
    matchingSameComponent bottomCount stateT firstIndex secondIndex
      = matchingSameComponent bottomCount stateS firstIndex secondIndex

/-- The simulation is reflexive. -/
theorem matchingConnectivityViewSim_refl (bottomCount : Nat) (state : WireState) :
    MatchingConnectivityViewSim bottomCount state state :=
  { lengthEq := rfl, loopsEq := rfl, viewAgrees := fun _ _ _ _ => rfl }

/-- ★ **The per-atom dispatch**: one cup/cap-disciplined atom preserves the view simulation
between two conditioned states.  The arity dichotomy selects the transport — the cup's window
bound (`position ≤ length`) and the cap's (`position + 2 ≤ length`) both read off the tracked
`domBoundaryLength` decomposition. -/
theorem matchingConnectivityViewSim_stepAtom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (stateS stateT : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (conditionsS : MatchingSwapStateConditions bottomCount stateS)
    (conditionsT : MatchingSwapStateConditions bottomCount stateT)
    (atomArity : AtomHasCupOrCapArity atom)
    (tracksEntry : stateS.openWires.length = atom.domBoundaryLength)
    (sim : MatchingConnectivityViewSim bottomCount stateT stateS) :
    MatchingConnectivityViewSim bottomCount (stepAtom stateT atom) (stepAtom stateS atom) := by
  cases atomArity with
  | inl cupArity =>
      rw [stepAtom_ofCupArity stateT atom cupArity.1 cupArity.2,
        stepAtom_ofCupArity stateS atom cupArity.1 cupArity.2]
      have positionLe : atom.leftContext.length ≤ stateS.openWires.length := by
        rw [tracksEntry]
        show atom.leftContext.length
          ≤ atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
        rw [cupArity.1]
        exact Nat.le_add_right (atom.leftContext.length + 0) atom.rightContext.length
      exact
        { lengthEq := matchingViewLength_stepCup stateS stateT atom.leftContext.length
            sim.lengthEq,
          loopsEq := matchingViewLoops_stepCup stateS stateT sim.loopsEq
            atom.leftContext.length,
          viewAgrees := matchingViewAgrees_stepCup bottomCount stateS stateT
            atom.leftContext.length positionLe sim.lengthEq conditionsS conditionsT
            sim.viewAgrees }
  | inr capArity =>
      rw [stepAtom_ofCapArity stateT atom capArity.1 capArity.2,
        stepAtom_ofCapArity stateS atom capArity.1 capArity.2]
      have windowLe : atom.leftContext.length + 2 ≤ stateS.openWires.length := by
        rw [tracksEntry]
        show atom.leftContext.length + 2
          ≤ atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
        rw [capArity.1]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      exact
        { lengthEq := matchingViewLength_stepCap stateS stateT atom.leftContext.length
            windowLe sim.lengthEq,
          loopsEq := matchingViewLoops_stepCap bottomCount stateS stateT
            atom.leftContext.length windowLe sim.loopsEq sim.viewAgrees,
          viewAgrees := matchingViewAgrees_stepCap bottomCount stateS stateT
            atom.leftContext.length windowLe sim.lengthEq conditionsS.forest
            conditionsT.forest sim.viewAgrees }

/-- ★ **The spine fold**: the view simulation is preserved by a whole boundary-disciplined
spine — conditions step by `matchingSwapStateConditions_stepAtom` on BOTH states, the chain
hands each atom its firing boundary, and the tracking steps by
`stepAtom_openWires_tracksBoundary`. -/
theorem matchingConnectivityViewSim_processSpine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) →
    (stateS stateT : WireState) → (boundaryLength : Nat) →
    MatchingSwapStateConditions bottomCount stateS →
    MatchingSwapStateConditions bottomCount stateT →
    SpineHasCupCapAtoms atoms →
    SpineBoundaryChained boundaryLength atoms →
    stateS.openWires.length = boundaryLength →
    MatchingConnectivityViewSim bottomCount stateT stateS →
    MatchingConnectivityViewSim bottomCount (processSpine stateT atoms)
      (processSpine stateS atoms)
  | [], _, _, _, _, _, _, _, _, sim => sim
  | atom :: rest, stateS, stateT, _, conditionsS, conditionsT, arity, chained, tracks,
      sim => by
    have headAndTail := spineBoundaryChained_tail chained
    have arityParts := spineHasCupCapAtoms_tail arity
    have tracksEntry : stateS.openWires.length = atom.domBoundaryLength :=
      tracks.trans headAndTail.1.symm
    exact matchingConnectivityViewSim_processSpine bottomCount rest
      (stepAtom stateS atom) (stepAtom stateT atom) atom.codBoundaryLength
      (matchingSwapStateConditions_stepAtom bottomCount stateS atom conditionsS)
      (matchingSwapStateConditions_stepAtom bottomCount stateT atom conditionsT)
      arityParts.2 headAndTail.2
      (stepAtom_openWires_tracksBoundary stateS atom arityParts.1 tracksEntry)
      (matchingConnectivityViewSim_stepAtom bottomCount stateS stateT atom conditionsS
        conditionsT arityParts.1 tracksEntry sim)

/-! ## Honesty marker -/

/-- **Honesty marker — the connectivity-view simulation is SHIPPED.**  The bundled relation
(`MatchingConnectivityViewSim`: length + loops + in-range view agreement), the per-atom
cup/cap dispatch onto the shipped stability transports, and the fold over any
boundary-disciplined spine (conditions + chain + tracking threaded exactly as in
`traceInvariant_of_boundaryDiscipline`).  NOT yet covered: the extract→view reconstruction
(equal `matchingOf` diagrams give a view sim at the run states) and the run-composition law
consuming this fold to inhabit the `MatchingSaturatedCongruence` fields — the remaining
MODE3-C bricks.  `= true`. -/
def fxMode_hasMatchingConnectivityViewSim : Bool := true

end FX1Poly.Polygraph
