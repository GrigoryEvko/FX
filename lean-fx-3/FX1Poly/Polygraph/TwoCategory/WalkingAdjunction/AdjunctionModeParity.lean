import FX1Poly.Polygraph.Computad.AdjunctionSeed

/-! # AdjunctionModeParity — the absolute mode formula: position parity determines the mode

The walking-adjunction quiver has exactly one modality out of each mode (`left` out of `base`,
`right` out of `tip`), so walking any path alternates modes strictly.  This file ships the
ABSOLUTE consequence the rigidity file (`AdjunctionPathRigidity`) leaves relative: the mode
reached after `distance` edges is a FUNCTION of the start mode and the distance's parity
(`adjunctionModeAtDistance`), and every path's target satisfies the formula
(`adjunctionPath_targetMode_eq_modeAtDistance`).

This is the peel campaign's typing substrate: boundary-path edge types at the walking
adjunction are pure parity data (the edge out of a `base` point is `left`, out of a `tip`
point is `right`), so the circle-freedom invariant and the window-typing refutations can be
stated on positions and parities alone — no path indexing, no threading of the boundary path
through the arc fold.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The other adjunction mode. -/
def adjunctionOppositeMode : AdjunctionMode → AdjunctionMode
  | AdjunctionMode.base => AdjunctionMode.tip
  | AdjunctionMode.tip => AdjunctionMode.base

/-- Swapping the mode twice returns the original. -/
theorem adjunctionOppositeMode_isInvolutive (mode : AdjunctionMode) :
    adjunctionOppositeMode (adjunctionOppositeMode mode) = mode := by
  cases mode with
  | base => rfl
  | tip => rfl

/-- Every seed modality lands on the OPPOSITE mode: `left` maps `base` to `tip`, `right` maps
`tip` to `base` — there are no endo-modalities at the seed. -/
theorem adjunctionModality_targetsOppositeMode {sourceMode targetMode : AdjunctionMode}
    (modality : AdjunctionModality sourceMode targetMode) :
    targetMode = adjunctionOppositeMode sourceMode := by
  cases modality with
  | left => rfl
  | right => rfl

/-- ★ The mode reached from `startMode` after walking `distance` seed edges — the parity
formula: even distances return the start mode, odd distances the opposite. -/
def adjunctionModeAtDistance (startMode : AdjunctionMode) : Nat → AdjunctionMode
  | 0 => startMode
  | distance + 1 => adjunctionOppositeMode (adjunctionModeAtDistance startMode distance)

/-- Walking from the opposite start commutes with taking the opposite of the destination —
the swap that lets the distance recursion (peeling at the far end) consume path cons
(peeling at the source end). -/
theorem adjunctionModeAtDistance_fromOppositeStart (startMode : AdjunctionMode) :
    ∀ distance : Nat,
      adjunctionModeAtDistance (adjunctionOppositeMode startMode) distance
        = adjunctionOppositeMode (adjunctionModeAtDistance startMode distance)
  | 0 => rfl
  | distance + 1 =>
      congrArg adjunctionOppositeMode
        (adjunctionModeAtDistance_fromOppositeStart startMode distance)

/-- Distances compose: walking `firstDistance + secondDistance` edges is walking them in
sequence — the parity formula for `composePath` lengths. -/
theorem adjunctionModeAtDistance_add (startMode : AdjunctionMode) (firstDistance : Nat) :
    ∀ secondDistance : Nat,
      adjunctionModeAtDistance startMode (firstDistance + secondDistance)
        = adjunctionModeAtDistance (adjunctionModeAtDistance startMode firstDistance)
            secondDistance
  | 0 => rfl
  | secondDistance + 1 =>
      congrArg adjunctionOppositeMode
        (adjunctionModeAtDistance_add startMode firstDistance secondDistance)

/-- ★ **The absolute mode formula.**  Every walking-adjunction path's target mode is
`adjunctionModeAtDistance` of its source and length: from each mode there is exactly one
outgoing modality, so the mode sequence along ANY path is the strict alternation. -/
theorem adjunctionPath_targetMode_eq_modeAtDistance :
    ∀ {sourceMode targetMode : adjunctionGraph.Mode}
      (path : ModalityPath adjunctionGraph sourceMode targetMode),
      targetMode = adjunctionModeAtDistance sourceMode path.length := by
  intro sourceMode targetMode path
  induction path with
  | nil startMode => rfl
  | @cons consSourceMode middleMode consTargetMode modality rest restHypothesis =>
      exact restHypothesis.trans
        ((congrArg (fun modeChoice => adjunctionModeAtDistance modeChoice rest.length)
            (adjunctionModality_targetsOppositeMode modality)).trans
          (adjunctionModeAtDistance_fromOppositeStart consSourceMode rest.length))

/-- **Honesty marker — the parity substrate is SHIPPED (peel campaign C, rung 1).**
`adjunctionModeAtDistance` + `adjunctionPath_targetMode_eq_modeAtDistance` pin every path's
mode sequence to start-mode-plus-parity, absolutely (the rigidity file's facts are relative:
parallel homs equal, equal lengths give equal targets).  Downstream: window typing (a cap
atom's window position has `tip` parity, a cup's `base` parity), the typed-ends circle-freedom
invariant on positions alone, and the head-cancellation reindexing.  What this marker does NOT
claim: the circle-freedom invariant itself, the partner location, or the head-cancellation —
the remaining peel rungs.  `= true`. -/
def fxMode_hasAdjunctionModeParity : Bool := true

end FX1Poly.Polygraph
