import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # SpinePositionShift — a left whisker's spine is a position-shifted copy

The matching action of one atom reads only the atom's SHAPE: its window position (the left
context's length) and its generator's arity (`MatchingSpineActionCongruence`).  A RIGHT
whisker leaves every shape untouched — that leg shipped as action-invisibility.  A LEFT
whisker extends every atom's left context by the whiskering 1-cell, so every window position
shifts by that 1-cell's length while the arities stay fixed.

This file reifies the LEFT leg's spine-level content:

* `SpinePositionShifted delta` — the pointwise correspondence between two atom lists (at
  possibly different overall boundary modes): equal length, equal generator arities, and
  every shifted position exactly `delta` ahead of its base position;
* `spineDiff_spinePositionShifted` — the difference-list master: running one cell through
  `spineDiff` with two left accumulators whose lengths differ by `delta` produces
  corresponded atom lists (cell induction; the left whisker preserves the length gap through
  `composePath_length`);
* `spine_whiskerLeft_spinePositionShifted` — the payoff instance: the spine of
  `whiskerLeft oneCell cell` is a `oneCell.length`-shifted copy of `cell.spine`.

The two-list boundary-disciplined fold carrying `MatchingLeftPadSim` through a corresponded
pair is the next brick. -/

namespace FX1Poly.Polygraph

/-! ## The pointwise position-shift correspondence -/

/-- ★ **Two atom lists correspond up to a uniform window shift**: pointwise, the shifted
atom's window position is exactly `delta` ahead of the base atom's, and the generator
arities agree.  The two lists may live at DIFFERENT overall boundary modes — exactly the
whiskered-versus-bare situation. -/
inductive SpinePositionShifted (delta : Nat) {signature : ModeSignature}
    {sourceModeBase targetModeBase sourceModeShifted targetModeShifted :
      signature.graph.Mode} :
    List (SpineAtom signature sourceModeBase targetModeBase) →
    List (SpineAtom signature sourceModeShifted targetModeShifted) → Prop where
  /-- Empty lists correspond. -/
  | nil : SpinePositionShifted delta [] []
  /-- Cons two atoms whose windows sit `delta` apart with equal generator arities. -/
  | cons (atomBase : SpineAtom signature sourceModeBase targetModeBase)
      (atomShifted : SpineAtom signature sourceModeShifted targetModeShifted)
      (restBase : List (SpineAtom signature sourceModeBase targetModeBase))
      (restShifted : List (SpineAtom signature sourceModeShifted targetModeShifted))
      (positionShifted : atomShifted.leftContext.length
        = delta + atomBase.leftContext.length)
      (domLengthsAgree : atomShifted.generatorDom.length = atomBase.generatorDom.length)
      (codLengthsAgree : atomShifted.generatorCod.length = atomBase.generatorCod.length)
      (restsCorrespond : SpinePositionShifted delta restBase restShifted) :
      SpinePositionShifted delta (atomBase :: restBase) (atomShifted :: restShifted)

/-! ## The difference-list master -/

/-- ★ **`spineDiff` at two left accumulators whose lengths differ by `delta` produces
position-shift-corresponded atom lists.**  Cell induction: a generator conses two atoms whose
left contexts ARE the accumulators (positions `delta` apart by hypothesis, arities equal
because the generator is shared), an identity passes the rest correspondence through, a
vertical composite chains through both factors, a left whisker extends both accumulators by
the same 1-cell (preserving the `delta` gap through `composePath_length`), and a right
whisker touches neither position nor arity. -/
theorem spineDiff_spinePositionShifted {signature : ModeSignature}
    {overallSourceBase overallTargetBase overallSourceShifted overallTargetShifted :
      signature.graph.Mode} (delta : Nat) :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccBase : ModalityPath signature.graph overallSourceBase localSource) →
    (rightAccBase : ModalityPath signature.graph localTarget overallTargetBase) →
    (leftAccShifted : ModalityPath signature.graph overallSourceShifted localSource) →
    (rightAccShifted : ModalityPath signature.graph localTarget overallTargetShifted) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (restBase : List (SpineAtom signature overallSourceBase overallTargetBase)) →
    (restShifted : List (SpineAtom signature overallSourceShifted overallTargetShifted)) →
    leftAccShifted.length = delta + leftAccBase.length →
    SpinePositionShifted delta restBase restShifted →
    SpinePositionShifted delta (cell.spineDiff leftAccBase rightAccBase restBase)
      (cell.spineDiff leftAccShifted rightAccShifted restShifted)
  | _, _, leftAccBase, rightAccBase, leftAccShifted, rightAccShifted, _, _, .gen generator,
      restBase, restShifted, accumulatorShift, restsCorrespond =>
      SpinePositionShifted.cons
        ⟨_, _, leftAccBase, _, _, generator, rightAccBase⟩
        ⟨_, _, leftAccShifted, _, _, generator, rightAccShifted⟩
        restBase restShifted accumulatorShift rfl rfl restsCorrespond
  | _, _, _, _, _, _, _, _, .id _, _, _, _, restsCorrespond => restsCorrespond
  | _, _, leftAccBase, rightAccBase, leftAccShifted, rightAccShifted, _, _,
      .vcomp cellAlpha cellBeta, restBase, restShifted, accumulatorShift, restsCorrespond =>
      spineDiff_spinePositionShifted delta leftAccBase rightAccBase leftAccShifted
        rightAccShifted cellAlpha
        (cellBeta.spineDiff leftAccBase rightAccBase restBase)
        (cellBeta.spineDiff leftAccShifted rightAccShifted restShifted) accumulatorShift
        (spineDiff_spinePositionShifted delta leftAccBase rightAccBase leftAccShifted
          rightAccShifted cellBeta restBase restShifted accumulatorShift restsCorrespond)
  | _, _, leftAccBase, rightAccBase, leftAccShifted, rightAccShifted, _, _,
      .whiskerLeft oneCell body, restBase, restShifted, accumulatorShift, restsCorrespond =>
      spineDiff_spinePositionShifted delta (composePath leftAccBase oneCell) rightAccBase
        (composePath leftAccShifted oneCell) rightAccShifted body restBase restShifted
        (by rw [composePath_length leftAccShifted oneCell,
          composePath_length leftAccBase oneCell, accumulatorShift,
          Nat.add_assoc delta leftAccBase.length oneCell.length])
        restsCorrespond
  | _, _, leftAccBase, rightAccBase, leftAccShifted, rightAccShifted, _, _,
      .whiskerRight oneCell body, restBase, restShifted, accumulatorShift, restsCorrespond =>
      spineDiff_spinePositionShifted delta leftAccBase (composePath oneCell rightAccBase)
        leftAccShifted (composePath oneCell rightAccShifted) body restBase restShifted
        accumulatorShift restsCorrespond

/-! ## The payoff: a left whisker's spine is a shifted copy -/

/-- ★ **The spine of `whiskerLeft oneCell cell` is a `oneCell.length`-shifted copy of
`cell.spine`.**  The whiskered spine unfolds definitionally to the cell's own `spineDiff`
with left accumulator `oneCell` (composed onto the empty accumulator), whose length is
`oneCell.length + 0` — so the master applies with a `rfl` length gap. -/
theorem spine_whiskerLeft_spinePositionShifted {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellF oneCellG : ModalityPath signature.graph middleMode targetMode}
    (cell : RawTwoCellExpr signature oneCellF oneCellG) :
    SpinePositionShifted oneCell.length cell.spine
      (RawTwoCellExpr.whiskerLeft oneCell cell).spine :=
  spineDiff_spinePositionShifted oneCell.length (identityPath middleMode)
    (identityPath targetMode) (composePath (identityPath sourceMode) oneCell)
    (identityPath targetMode) cell [] [] rfl SpinePositionShifted.nil

/-! ## Honesty marker -/

/-- **Honesty marker — the left-whisker spine correspondence is SHIPPED.**  The pointwise
`SpinePositionShifted` relation, the `spineDiff` master over any `delta`-gapped left
accumulators, and the `whiskerLeft` instance at gap `oneCell.length`.  The two-list
boundary-disciplined fold carrying `MatchingLeftPadSim` through a corresponded pair is the
next brick.  `= true`. -/
def fxMode_hasSpinePositionShift : Bool := true

end FX1Poly.Polygraph
