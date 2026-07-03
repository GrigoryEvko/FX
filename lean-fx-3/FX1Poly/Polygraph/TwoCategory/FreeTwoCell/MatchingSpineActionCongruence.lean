import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # MatchingSpineActionCongruence — the matching action reads only the spine's shape

`stepAtom` computes from an atom's left-context LENGTH (the window position) and its
generator's arity — never from the right context, the accumulator payloads, or the overall
boundary modes.  This file reifies that observation:

* `matchingShapeAction` — the per-atom action as a function of the three shape numbers, with
  `stepAtom_eq_matchingShapeAction` the definitional read-off;
* `stepAtom_congrOfShape` — two atoms of equal shape (possibly at DIFFERENT overall modes)
  step any state identically;
* `processSpine_spineDiff_congrOfLeftLength` — the whole difference-list action depends only
  on the left accumulator's length (cell induction; the left whisker preserves the length
  hypothesis through `composePath_length`);
* `processSpine_spine_whiskerRight` — the payoff: a RIGHT whisker is matching-action-invisible,
  collapsing the padded `whiskerRight` run onto the bare cell's own spine.

This is the reduction that lets the right-padded simulation (`MatchingRightPadSim`) compare
`matchingOf (whiskerRight oneCell alpha)` with `matchingOf alpha` as TWO SEEDS of ONE spine —
the `whiskerRightCongruent` assembly is the next brick. -/

namespace FX1Poly.Polygraph

/-! ## The shape action -/

/-- The matching action of one atom as a function of its SHAPE only: the window position and
the generator's consumed/produced arities. -/
def matchingShapeAction (state : WireState) (position numConsumed numProduced : Nat) :
    WireState :=
  match numConsumed, numProduced with
  | 0, 2 => stepCup state position
  | 2, 0 => stepCap state position
  | numConsumed, numProduced =>
      { openWires := natListInsertAt
          (Nat.rec state.openWires
            (fun _ shorterWires => natListRemoveTwoAt shorterWires position) numConsumed)
          position ((List.range numProduced).map (· + state.nextFresh))
        links := state.links
        nextFresh := state.nextFresh + numProduced
        loops := state.loops }

/-- `stepAtom` IS the shape action at the atom's shape numbers — definitional read-off. -/
theorem stepAtom_eq_matchingShapeAction {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (state : WireState)
    (atom : SpineAtom signature sourceMode targetMode) :
    stepAtom state atom
      = matchingShapeAction state atom.leftContext.length atom.generatorDom.length
          atom.generatorCod.length := rfl

/-- ★ **The per-atom matching action reads only the atom's shape.**  Two atoms agreeing on
window position and generator arity — in particular the same generator under DIFFERENT
whiskering accumulators, even at different overall modes — step any state identically. -/
theorem stepAtom_congrOfShape {signature : ModeSignature}
    {sourceModeOne targetModeOne sourceModeTwo targetModeTwo : signature.graph.Mode}
    (state : WireState)
    (atomOne : SpineAtom signature sourceModeOne targetModeOne)
    (atomTwo : SpineAtom signature sourceModeTwo targetModeTwo)
    (positionEq : atomOne.leftContext.length = atomTwo.leftContext.length)
    (domLenEq : atomOne.generatorDom.length = atomTwo.generatorDom.length)
    (codLenEq : atomOne.generatorCod.length = atomTwo.generatorCod.length) :
    stepAtom state atomOne = stepAtom state atomTwo := by
  rw [stepAtom_eq_matchingShapeAction state atomOne,
    stepAtom_eq_matchingShapeAction state atomTwo, positionEq, domLenEq, codLenEq]

/-! ## The difference-list action congruence -/

/-- ★ **The matching action of a spine difference-list depends only on the LEFT accumulator's
LENGTH** — never on the right accumulator, the accumulator payloads, or the overall boundary
modes.  Cell induction: a generator steps by shape, an identity is inert, a vertical composite
chains through both factors, a left whisker preserves the length hypothesis through
`composePath_length`, a right whisker changes nothing the action can see. -/
theorem processSpine_spineDiff_congrOfLeftLength {signature : ModeSignature}
    {overallSourceOne overallTargetOne overallSourceTwo overallTargetTwo :
      signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccOne : ModalityPath signature.graph overallSourceOne localSource) →
    (rightAccOne : ModalityPath signature.graph localTarget overallTargetOne) →
    (leftAccTwo : ModalityPath signature.graph overallSourceTwo localSource) →
    (rightAccTwo : ModalityPath signature.graph localTarget overallTargetTwo) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (restOne : List (SpineAtom signature overallSourceOne overallTargetOne)) →
    (restTwo : List (SpineAtom signature overallSourceTwo overallTargetTwo)) →
    leftAccOne.length = leftAccTwo.length →
    (∀ innerState : WireState,
      processSpine innerState restOne = processSpine innerState restTwo) →
    ∀ state : WireState,
      processSpine state (cell.spineDiff leftAccOne rightAccOne restOne)
        = processSpine state (cell.spineDiff leftAccTwo rightAccTwo restTwo)
  | _, _, leftAccOne, rightAccOne, leftAccTwo, rightAccTwo, _, _, .gen generator, restOne,
      restTwo, positionEq, restActionEq, state => by
      show processSpine
          (stepAtom state ⟨_, _, leftAccOne, _, _, generator, rightAccOne⟩) restOne
        = processSpine
          (stepAtom state ⟨_, _, leftAccTwo, _, _, generator, rightAccTwo⟩) restTwo
      rw [stepAtom_congrOfShape state ⟨_, _, leftAccOne, _, _, generator, rightAccOne⟩
        ⟨_, _, leftAccTwo, _, _, generator, rightAccTwo⟩ positionEq rfl rfl]
      exact restActionEq (stepAtom state ⟨_, _, leftAccTwo, _, _, generator, rightAccTwo⟩)
  | _, _, _, _, _, _, _, _, .id _, _, _, _, restActionEq, state => restActionEq state
  | _, _, leftAccOne, rightAccOne, leftAccTwo, rightAccTwo, _, _, .vcomp cellAlpha cellBeta,
      restOne, restTwo, positionEq, restActionEq, state =>
      processSpine_spineDiff_congrOfLeftLength leftAccOne rightAccOne leftAccTwo rightAccTwo
        cellAlpha (cellBeta.spineDiff leftAccOne rightAccOne restOne)
        (cellBeta.spineDiff leftAccTwo rightAccTwo restTwo) positionEq
        (processSpine_spineDiff_congrOfLeftLength leftAccOne rightAccOne leftAccTwo
          rightAccTwo cellBeta restOne restTwo positionEq restActionEq)
        state
  | _, _, leftAccOne, rightAccOne, leftAccTwo, rightAccTwo, _, _,
      .whiskerLeft oneCell body, restOne, restTwo, positionEq, restActionEq, state =>
      processSpine_spineDiff_congrOfLeftLength (composePath leftAccOne oneCell) rightAccOne
        (composePath leftAccTwo oneCell) rightAccTwo body restOne restTwo
        (by rw [composePath_length leftAccOne oneCell,
          composePath_length leftAccTwo oneCell, positionEq])
        restActionEq state
  | _, _, leftAccOne, rightAccOne, leftAccTwo, rightAccTwo, _, _,
      .whiskerRight oneCell body, restOne, restTwo, positionEq, restActionEq, state =>
      processSpine_spineDiff_congrOfLeftLength leftAccOne (composePath oneCell rightAccOne)
        leftAccTwo (composePath oneCell rightAccTwo) body restOne restTwo positionEq
        restActionEq state

/-! ## The payoff: a right whisker is matching-action-invisible -/

/-- ★ **A RIGHT whisker is invisible to the matching action**: the whiskered cell's spine
steps every state exactly as the bare cell's own spine does — `stepAtom` never reads the
right context, and a right whisker touches nothing else. -/
theorem processSpine_spine_whiskerRight {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    (cell : RawTwoCellExpr signature oneCellF oneCellG) (state : WireState) :
    processSpine state (RawTwoCellExpr.whiskerRight oneCell cell).spine
      = processSpine state cell.spine :=
  processSpine_spineDiff_congrOfLeftLength (identityPath sourceMode)
    (composePath oneCell (identityPath targetMode)) (identityPath sourceMode)
    (identityPath middleMode) cell [] [] rfl (fun _ => rfl) state

/-- **Honesty marker — the matching action is spine-shape-determined.**  The per-atom action
is a function of window position + generator arity (`matchingShapeAction`), the difference-list
action depends only on the left accumulator's length, and a right whisker is action-invisible.
NOT yet shipped: the padded-boundary view read-off and the `whiskerRightCongruent` assembly —
the next MODE3-C bricks.  `= true`. -/
def fxMode_hasMatchingSpineActionCongruence : Bool := true

end FX1Poly.Polygraph
