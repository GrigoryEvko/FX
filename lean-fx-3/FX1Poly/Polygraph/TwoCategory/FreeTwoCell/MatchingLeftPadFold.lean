import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpinePositionShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline

/-! # MatchingLeftPadFold — the left-padded sim folds over a position-shifted spine pair

The right-pad fold ran ONE atom list against two seeds (a right whisker is action-invisible).
The left leg genuinely runs TWO lists: the base spine on the base state and its
position-shifted copy (`SpinePositionShifted`, the whiskered spine) on the padded state, each
shifted atom firing at the `delta`-offset window.  This file installs the two-list fold:

* `matchingLeftPadSim_step_ofCorrespondence` — one corresponded atom pair steps the
  simulation: arity agreement transports the base atom's cup/cap dispatch to the shifted
  atom, and the position shift lands exactly on the `MatchingLeftPadSim` step lemmas'
  `delta + position` window;
* `matchingLeftPadSim_processSpine_ofCorrespondence` — the fold, by structural induction on
  the correspondence, threading the boundary chain + cup/cap arity + wire-count tracking of
  the BASE side exactly as in the right-pad fold.

The left canonical-seed instance and the padded-boundary read-off are the next bricks. -/

namespace FX1Poly.Polygraph

/-- ★ **One corresponded atom pair steps the left-padded simulation.**  The base atom's
cup/cap arity transports to the shifted atom through the arity agreements, so both dispatch
to the same step; the position shift rewrites the shifted atom's window to
`delta + basePosition`, which is exactly where the left-pad step lemmas fire. -/
theorem matchingLeftPadSim_step_ofCorrespondence {signature : ModeSignature}
    {sourceModeBase targetModeBase sourceModeShifted targetModeShifted :
      signature.graph.Mode}
    (delta : Nat) (padPrefix : List Nat) (stateS stateT : WireState)
    (atomBase : SpineAtom signature sourceModeBase targetModeBase)
    (atomShifted : SpineAtom signature sourceModeShifted targetModeShifted)
    (positionShifted : atomShifted.leftContext.length
      = delta + atomBase.leftContext.length)
    (domLengthsAgree : atomShifted.generatorDom.length = atomBase.generatorDom.length)
    (codLengthsAgree : atomShifted.generatorCod.length = atomBase.generatorCod.length)
    (arity : AtomHasCupOrCapArity atomBase)
    (windowInRange : atomBase.leftContext.length + atomBase.generatorDom.length
      ≤ stateS.openWires.length)
    (sim : MatchingLeftPadSim delta padPrefix stateS stateT) :
    MatchingLeftPadSim delta padPrefix
      (stepAtom stateS atomBase) (stepAtom stateT atomShifted) := by
  cases arity with
  | inl cupArity =>
      rw [stepAtom_ofCupArity stateS atomBase cupArity.1 cupArity.2,
        stepAtom_ofCupArity stateT atomShifted (domLengthsAgree.trans cupArity.1)
          (codLengthsAgree.trans cupArity.2),
        positionShifted]
      exact matchingLeftPadSim_stepCup delta padPrefix stateS stateT
        atomBase.leftContext.length sim
  | inr capArity =>
      rw [stepAtom_ofCapArity stateS atomBase capArity.1 capArity.2,
        stepAtom_ofCapArity stateT atomShifted (domLengthsAgree.trans capArity.1)
          (codLengthsAgree.trans capArity.2),
        positionShifted]
      rw [capArity.1] at windowInRange
      exact matchingLeftPadSim_stepCap delta padPrefix stateS stateT
        atomBase.leftContext.length
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self (atomBase.leftContext.length + 1))
          windowInRange)
        sim

/-- ★ **The left-padded sim folds over a position-shifted spine pair under the base side's
boundary discipline** — structural induction on the correspondence; the chain, arity, and
wire-count tracking thread on the BASE run exactly as in the right-pad fold, and each pair
steps through `matchingLeftPadSim_step_ofCorrespondence`. -/
theorem matchingLeftPadSim_processSpine_ofCorrespondence {signature : ModeSignature}
    {sourceModeBase targetModeBase sourceModeShifted targetModeShifted :
      signature.graph.Mode} (delta : Nat) (padPrefix : List Nat) :
    (atomsBase : List (SpineAtom signature sourceModeBase targetModeBase)) →
    (atomsShifted : List (SpineAtom signature sourceModeShifted targetModeShifted)) →
    (stateS stateT : WireState) → (boundaryLength : Nat) →
    SpinePositionShifted delta atomsBase atomsShifted →
    SpineBoundaryChained boundaryLength atomsBase →
    SpineHasCupCapAtoms atomsBase →
    stateS.openWires.length = boundaryLength →
    MatchingLeftPadSim delta padPrefix stateS stateT →
    MatchingLeftPadSim delta padPrefix
      (processSpine stateS atomsBase) (processSpine stateT atomsShifted)
  | _, _, _, _, _, .nil, _, _, _, sim => sim
  | _, _, stateS, stateT, boundaryLength,
      .cons atomBase atomShifted restBase restShifted positionShifted domLengthsAgree
        codLengthsAgree restsCorrespond, chained, arity, tracks, sim => by
      show MatchingLeftPadSim delta padPrefix
        (processSpine (stepAtom stateS atomBase) restBase)
        (processSpine (stepAtom stateT atomShifted) restShifted)
      have headAndTail := spineBoundaryChained_tail chained
      have arityParts := spineHasCupCapAtoms_tail arity
      have windowInRange : atomBase.leftContext.length + atomBase.generatorDom.length
          ≤ stateS.openWires.length := by
        rw [tracks, ← headAndTail.1]
        exact Nat.le_add_right
          (atomBase.leftContext.length + atomBase.generatorDom.length)
          atomBase.rightContext.length
      exact matchingLeftPadSim_processSpine_ofCorrespondence delta padPrefix restBase
        restShifted (stepAtom stateS atomBase) (stepAtom stateT atomShifted)
        atomBase.codBoundaryLength restsCorrespond headAndTail.2 arityParts.2
        (stepAtom_openWires_tracksBoundary stateS atomBase arityParts.1
          (tracks.trans headAndTail.1.symm))
        (matchingLeftPadSim_step_ofCorrespondence delta padPrefix stateS stateT atomBase
          atomShifted positionShifted domLengthsAgree codLengthsAgree arityParts.1
          windowInRange sim)

/-! ## Honesty marker -/

/-- **Honesty marker — the left-padded two-list fold is SHIPPED.**  One corresponded atom
pair steps the simulation (arity transported, window at `delta + position`), and the whole
position-shifted spine pair folds under the base side's chain + cup/cap discipline.  The
left canonical-seed instance, the padded-boundary read-off, and the whiskerLeft assembly are
the next bricks.  `= true`. -/
def fxMode_hasMatchingLeftPadFold : Bool := true

end FX1Poly.Polygraph
