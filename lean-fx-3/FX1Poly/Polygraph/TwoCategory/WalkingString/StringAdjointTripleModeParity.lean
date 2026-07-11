import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine

/-! # WalkingString/StringAdjointTripleModeParity — the absolute mode formula at the adjoint triple (FC-3 r22, B2 P1)

The walking-adjoint-triple quiver has, out of each mode, only mode-flipping modalities (`left`/`coLeft` out of
`base`, `right` out of `tip`), so walking ANY path alternates modes strictly.  This is the string clone of
`WalkingAdjunction/AdjunctionModeParity`: the mode reached after `distance` edges is a FUNCTION of the start mode
and the distance parity (`adjointTripleModeAtDistance`), and every path's target satisfies the formula
(`adjointTripleModalityPath_targetMode_eq_modeAtDistance`).  The only delta from the adjunction original is the
THREE-way modality case split (`left`/`right`/`coLeft` instead of `left`/`right`); every modality still lands on
the opposite mode, so the parity arithmetic is identical.

This is the parity substrate the descent's seat/refute bookkeeping rides:

  * `adjointTripleModeAtDistance` + `adjointTripleModalityPath_targetMode_eq_modeAtDistance` — every path's mode
    sequence is start-mode-plus-parity, absolutely;
  * `adjointTripleModeAtDistance_stableUnderTwoShift` — parities survive a two-shift (every cup inserts two wires,
    every cap removes two), so a surviving open end's mode is unchanged by the fold reindexing;
  * `adjointTripleAtom_windowPositionMode` — an atom's window position mode is its `leftMidMode` (through the
    absolute formula on the left context).  COLOUR NOTE: unlike the single adjunction (cup at `base`, cap at
    `tip`), at the triple a cap can seat at either parity — `counitLower` (window `G·F`) at `tip`, `counitUpper`
    (window `H·G`) at `base` — so the correct pin is `leftMidMode`, not a fixed `base`/`tip`.

Raw Lean 4 + Init; the parity recursion is structural on the distance and on the path.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The other adjoint-triple mode. -/
def adjointTripleOppositeMode : AdjointTripleMode → AdjointTripleMode
  | AdjointTripleMode.base => AdjointTripleMode.tip
  | AdjointTripleMode.tip => AdjointTripleMode.base

/-- Swapping the mode twice returns the original. -/
theorem adjointTripleOppositeMode_isInvolutive (mode : AdjointTripleMode) :
    adjointTripleOppositeMode (adjointTripleOppositeMode mode) = mode := by
  cases mode with
  | base => rfl
  | tip => rfl

/-- Every seed modality lands on the OPPOSITE mode: `left`/`coLeft` map `base` to `tip`, `right` maps `tip` to
`base` — there are no endo-modalities at the seed.  (The THREE-way split is the only delta from the single
adjunction, where there are two modalities.) -/
theorem adjointTripleModality_targetsOppositeMode {sourceMode targetMode : AdjointTripleMode}
    (modality : AdjointTripleModality sourceMode targetMode) :
    targetMode = adjointTripleOppositeMode sourceMode := by
  cases modality with
  | left => rfl
  | right => rfl
  | coLeft => rfl

/-- ★ The mode reached from `startMode` after walking `distance` seed edges — the parity formula: even distances
return the start mode, odd distances the opposite. -/
def adjointTripleModeAtDistance (startMode : AdjointTripleMode) : Nat → AdjointTripleMode
  | 0 => startMode
  | distance + 1 => adjointTripleOppositeMode (adjointTripleModeAtDistance startMode distance)

/-- Walking from the opposite start commutes with taking the opposite of the destination — the swap that lets the
distance recursion (peeling at the far end) consume path cons (peeling at the source end). -/
theorem adjointTripleModeAtDistance_fromOppositeStart (startMode : AdjointTripleMode) :
    ∀ distance : Nat,
      adjointTripleModeAtDistance (adjointTripleOppositeMode startMode) distance
        = adjointTripleOppositeMode (adjointTripleModeAtDistance startMode distance)
  | 0 => rfl
  | distance + 1 =>
      congrArg adjointTripleOppositeMode
        (adjointTripleModeAtDistance_fromOppositeStart startMode distance)

/-- Distances compose: walking `firstDistance + secondDistance` edges is walking them in sequence — the parity
formula for `composePath` lengths. -/
theorem adjointTripleModeAtDistance_add (startMode : AdjointTripleMode) (firstDistance : Nat) :
    ∀ secondDistance : Nat,
      adjointTripleModeAtDistance startMode (firstDistance + secondDistance)
        = adjointTripleModeAtDistance (adjointTripleModeAtDistance startMode firstDistance)
            secondDistance
  | 0 => rfl
  | secondDistance + 1 =>
      congrArg adjointTripleOppositeMode
        (adjointTripleModeAtDistance_add startMode firstDistance secondDistance)

/-- ★ **The absolute mode formula.**  Every walking-adjoint-triple path's target mode is
`adjointTripleModeAtDistance` of its source and length: from each mode every outgoing modality flips the mode, so
the mode sequence along ANY path is the strict alternation. -/
theorem adjointTripleModalityPath_targetMode_eq_modeAtDistance :
    ∀ {sourceMode targetMode : adjointTripleGraph.Mode}
      (path : ModalityPath adjointTripleGraph sourceMode targetMode),
      targetMode = adjointTripleModeAtDistance sourceMode path.length := by
  intro sourceMode targetMode path
  induction path with
  | nil startMode => rfl
  | @cons consSourceMode middleMode consTargetMode modality rest restHypothesis =>
      exact restHypothesis.trans
        ((congrArg (fun modeChoice => adjointTripleModeAtDistance modeChoice rest.length)
            (adjointTripleModality_targetsOppositeMode modality)).trans
          (adjointTripleModeAtDistance_fromOppositeStart consSourceMode rest.length))

/-- Position parity survives a two-shift: every cup inserts two wires and every cap removes two, so a surviving
open end's mode is unchanged by the reindexing. -/
theorem adjointTripleModeAtDistance_stableUnderTwoShift (startMode : AdjointTripleMode)
    (distance : Nat) :
    adjointTripleModeAtDistance startMode (distance + 2)
      = adjointTripleModeAtDistance startMode distance :=
  adjointTripleOppositeMode_isInvolutive (adjointTripleModeAtDistance startMode distance)

/-- ★ **The atom window position mode.**  An atom's window position mode is its `leftMidMode` — the target of
the left context, read off the absolute formula.  COLOUR NOTE: at the single adjunction a cup seats at `base`
and a cap at `tip`; at the adjoint triple a cap can seat at either parity (`counitLower` at `tip`, `counitUpper`
at `base`), so the pin is `leftMidMode`, not a fixed mode.  Downstream refutations read the seat mode off this. -/
theorem adjointTripleAtom_windowPositionMode
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atom : SpineAtom adjointTripleModeSignature overallSource overallTarget) :
    adjointTripleModeAtDistance overallSource atom.leftContext.length = atom.leftMidMode :=
  (adjointTripleModalityPath_targetMode_eq_modeAtDistance atom.leftContext).symm

/-- **Honesty marker — the adjoint-triple parity substrate is SHIPPED (FC-3 r22, B2 P1).**
`adjointTripleModeAtDistance` + `adjointTripleModalityPath_targetMode_eq_modeAtDistance` pin every path's mode
sequence to start-mode-plus-parity, absolutely; `adjointTripleModeAtDistance_stableUnderTwoShift` keeps parities
under the fold's two-shift; `adjointTripleAtom_windowPositionMode` reads an atom's window mode off its
`leftMidMode`.  The clean clone of `AdjunctionModeParity`, its only delta the three-way modality split.  What
this marker does NOT claim: the open-ends discipline, the seated descent, or the read-off — the remaining descent
rungs (P2 onward).  `= true`. -/
def fxString_hasAdjointTripleModeParity : Bool := true

end FX1Poly.Polygraph
