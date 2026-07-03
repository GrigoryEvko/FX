import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerReconstruction
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCounterShift
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingBoundaryDiscipline

/-! # mode-3 — the vcomp-LEFT matching congruence (the first `MatchingSaturatedCongruence` field)

The reconstruction (`matchingConnectivityViewSim_ofExtractEq`), the fold
(`matchingConnectivityViewSim_processSpine`), and the forward extraction
(`extractDiagram_eq_of_connectivityView`) chain into the LEFT-factor compositionality of the
matching: two cells with equal matchings stay matching-equal after post-composing any third
cell.

  * `RawTwoCellExpr.spine_vcomp` — the run-composition law: a vertical composite's spine is
    its factors' spines appended (the difference-list normalized);
  * `processSpine_append` — the fold splits over append;
  * ★ `extractAfterProcessing_vcompLeft_ofSeed` — the seed-generic core: from any conditioned
    seed reading the shared source boundary, extract equality of the α-runs reconstructs the
    connectivity-view simulation at the post-α states, the β-spine fold carries it (the entry
    tracking reads off the window-suffix invariant), and the forward extraction lands the
    composite extract equality;
  * ★ `matchingOf_vcompLeft_congruence` — the field inhabitant at the walking adjunction:
    boundary-dispatched (canonical seed when the source boundary is inhabited, the MODE3-B
    counter-shift proxy when it is empty), with the cup/cap discipline supplied by
    `cellHasCupCapGenerators_ofAdjunctionSignature`.

NOT covered here (honesty): the RIGHT-factor congruence — its premise lives at cellBeta's OWN
canonical seed while the composite runs cellBeta from the post-α state, so it needs the
action-factors-through-the-diagram compositionality (the Joyal–Street leg), not this chain.
The whisker fields are boundary-padding compositionality — also separate bricks.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Nat + range plumbing (hand-rolled; core equivalents leak propext) -/

private theorem natAddRightCancel : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled = rightSum + cancelled → leftSum = rightSum
  | 0, _, _, sumsEq => sumsEq
  | cancelled + 1, _, _, sumsEq => natAddRightCancel cancelled (Nat.succ.inj sumsEq)

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## The run-composition law -/

/-- **The run-composition law**: a vertical composite's spine is its factors' spines appended
— the difference-list continuation normalized through `spineDiff_append`. -/
theorem RawTwoCellExpr.spine_vcomp {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
    (RawTwoCellExpr.vcomp cellAlpha cellBeta).spine = cellAlpha.spine ++ cellBeta.spine := by
  show cellAlpha.spineDiff (identityPath sourceMode) (identityPath targetMode)
        (cellBeta.spineDiff (identityPath sourceMode) (identityPath targetMode) [])
      = cellAlpha.spineDiff (identityPath sourceMode) (identityPath targetMode) []
        ++ cellBeta.spineDiff (identityPath sourceMode) (identityPath targetMode) []
  exact RawTwoCellExpr.spineDiff_append (identityPath sourceMode) (identityPath targetMode)
    cellAlpha (cellBeta.spineDiff (identityPath sourceMode) (identityPath targetMode) [])

/-- The matching fold splits over atom-list concatenation. -/
theorem processSpine_append {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atomsOne atomsTwo : List (SpineAtom signature sourceMode targetMode)) →
    (state : WireState) →
    processSpine state (atomsOne ++ atomsTwo)
      = processSpine (processSpine state atomsOne) atomsTwo
  | [], _, _ => rfl
  | atom :: restAtoms, atomsTwo, state =>
      processSpine_append restAtoms atomsTwo (stepAtom state atom)

/-! ## The seed-generic core -/

/-- ★ **The seed-generic vcomp-LEFT extract congruence.**  From any conditioned seed whose
open-wire count reads the shared source boundary: equal α-run extracts reconstruct the
connectivity-view simulation at the post-α states (`matchingConnectivityViewSim_ofExtractEq`),
the β-spine fold transports it (`matchingConnectivityViewSim_processSpine`, with the entry
tracking read off the window-suffix length invariant), and the forward extraction
(`extractDiagram_eq_of_connectivityView`) lands the composite extract equality. -/
theorem extractAfterProcessing_vcompLeft_ofSeed {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    {cellAlphaFirst cellAlphaSecond : RawTwoCellExpr signature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
    (bottomCount : Nat) (seed : WireState)
    (seedConditions : MatchingSwapStateConditions bottomCount seed)
    (seedTracks : seed.openWires.length = oneCellF.length)
    (alphaSecondCupCap : CellHasCupCapGenerators cellAlphaSecond)
    (betaCupCap : CellHasCupCapGenerators cellBeta)
    (extractsEqual : extractDiagram bottomCount (processSpine seed cellAlphaFirst.spine)
        = extractDiagram bottomCount (processSpine seed cellAlphaSecond.spine)) :
    extractDiagram bottomCount
        (processSpine seed (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spine)
      = extractDiagram bottomCount
          (processSpine seed (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spine) := by
  rw [RawTwoCellExpr.spine_vcomp cellAlphaFirst cellBeta,
    RawTwoCellExpr.spine_vcomp cellAlphaSecond cellBeta,
    processSpine_append cellAlphaFirst.spine cellBeta.spine seed,
    processSpine_append cellAlphaSecond.spine cellBeta.spine seed]
  have viewSim := matchingConnectivityViewSim_ofExtractEq bottomCount
    (processSpine seed cellAlphaFirst.spine) (processSpine seed cellAlphaSecond.spine)
    extractsEqual
  have conditionsFirst := matchingSwapStateConditions_processSpine bottomCount
    cellAlphaFirst.spine seed seedConditions
  have conditionsSecond := matchingSwapStateConditions_processSpine bottomCount
    cellAlphaSecond.spine seed seedConditions
  have betaArity : SpineHasCupCapAtoms cellBeta.spine :=
    cellBeta.spineHasCupCapAtoms_spine betaCupCap
  have betaChained : SpineBoundaryChained oneCellG.length cellBeta.spine :=
    cellBeta.spineBoundaryChained_spine
  have windowInRange : (identityPath sourceMode).length + oneCellF.length
      ≤ seed.openWires.length := by
    show 0 + oneCellF.length ≤ seed.openWires.length
    rw [Nat.zero_add]
    exact Nat.le_of_eq seedTracks.symm
  have suffixInvariant := (runMatchingCell_openWiresSuffix_invariant
    (identityPath sourceMode) (identityPath targetMode) cellAlphaSecond seed
    alphaSecondCupCap windowInRange).2
  have tracks : (processSpine seed cellAlphaSecond.spine).openWires.length
      = oneCellG.length := by
    have lengthBalance : (processSpine seed cellAlphaSecond.spine).openWires.length
        + oneCellF.length = seed.openWires.length + oneCellG.length := suffixInvariant
    rw [seedTracks, Nat.add_comm oneCellF.length oneCellG.length] at lengthBalance
    exact natAddRightCancel oneCellF.length lengthBalance
  have foldedSim := matchingConnectivityViewSim_processSpine bottomCount cellBeta.spine
    (processSpine seed cellAlphaSecond.spine) (processSpine seed cellAlphaFirst.spine)
    oneCellG.length conditionsSecond conditionsFirst betaArity betaChained tracks viewSim
  refine extractDiagram_eq_of_connectivityView bottomCount
    (processSpine (processSpine seed cellAlphaFirst.spine) cellBeta.spine)
    (processSpine (processSpine seed cellAlphaSecond.spine) cellBeta.spine)
    foldedSim.lengthEq foldedSim.loopsEq ?_
  intro firstIndex secondIndex firstBound secondBound
  refine foldedSim.viewAgrees firstIndex secondIndex ?_ ?_
  · rw [← foldedSim.lengthEq]
    exact firstBound
  · rw [← foldedSim.lengthEq]
    exact secondBound

/-! ## The field inhabitant at the walking adjunction -/

/-- The canonical matching seed at a source boundary (the state `matchingOfSpineList` folds
from), named so record literals stay single-line. -/
private def canonicalMatchingSeed (bottomCount : Nat) : WireState :=
  { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }

/-- ★ **The vcomp-LEFT matching congruence at the walking adjunction** — the first
`MatchingSaturatedCongruence` field, unconditional.  The cup/cap discipline is universal over
the adjunction signature; the boundary dispatches between the canonical seed (inhabited
source boundary — the initial conditions package applies) and the MODE3-B counter-shift proxy
`⟨[], [], 1, 0⟩` (empty boundary — the degenerate seed is exchanged on the α-runs and the
composite runs, and the core chain fires from the proxy). -/
theorem matchingOf_vcompLeft_congruence {sourceMode targetMode : AdjunctionMode}
    {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellAlphaFirst cellAlphaSecond : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH)
    (matchingsEqual : matchingOf cellAlphaFirst = matchingOf cellAlphaSecond) :
    matchingOf (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta)
      = matchingOf (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta) := by
  show extractDiagram oneCellF.length
      (processSpine (canonicalMatchingSeed oneCellF.length)
        (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spine)
    = extractDiagram oneCellF.length
        (processSpine (canonicalMatchingSeed oneCellF.length)
          (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spine)
  have extractsEqual : extractDiagram oneCellF.length
      (processSpine (canonicalMatchingSeed oneCellF.length) cellAlphaFirst.spine)
    = extractDiagram oneCellF.length
        (processSpine (canonicalMatchingSeed oneCellF.length) cellAlphaSecond.spine) :=
    matchingsEqual
  cases Nat.lt_or_ge 0 oneCellF.length with
  | inl boundaryInhabited =>
      exact extractAfterProcessing_vcompLeft_ofSeed cellBeta oneCellF.length
        (canonicalMatchingSeed oneCellF.length)
        (matchingSwapStateConditions_initial oneCellF.length boundaryInhabited)
        (rangeLength oneCellF.length)
        (cellHasCupCapGenerators_ofAdjunctionSignature cellAlphaSecond)
        (cellHasCupCapGenerators_ofAdjunctionSignature cellBeta)
        extractsEqual
  | inr boundaryAtMostZero =>
      have zeroLength : oneCellF.length = 0 :=
        Nat.le_antisymm boundaryAtMostZero (Nat.zero_le oneCellF.length)
      rw [zeroLength]
      rw [zeroLength] at extractsEqual
      have shiftAlphaFirst : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            cellAlphaFirst.spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              cellAlphaFirst.spine) :=
        extractAfterProcessing_emptyBoundary_counterShift cellAlphaFirst.spine
          (zeroLength ▸ cellAlphaFirst.spineBoundaryChained_spine)
          (cellAlphaFirst.spineHasCupCapAtoms_spine
            (cellHasCupCapGenerators_ofAdjunctionSignature cellAlphaFirst))
      have shiftAlphaSecond : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            cellAlphaSecond.spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              cellAlphaSecond.spine) :=
        extractAfterProcessing_emptyBoundary_counterShift cellAlphaSecond.spine
          (zeroLength ▸ cellAlphaSecond.spineBoundaryChained_spine)
          (cellAlphaSecond.spineHasCupCapAtoms_spine
            (cellHasCupCapGenerators_ofAdjunctionSignature cellAlphaSecond))
      have shiftCompositeFirst : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spine) :=
        extractAfterProcessing_emptyBoundary_counterShift
          (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spine
          (zeroLength ▸ (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spineBoundaryChained_spine)
          ((RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spineHasCupCapAtoms_spine
            (cellHasCupCapGenerators_ofAdjunctionSignature
              (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta)))
      have shiftCompositeSecond : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spine) :=
        extractAfterProcessing_emptyBoundary_counterShift
          (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spine
          (zeroLength ▸ (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spineBoundaryChained_spine)
          ((RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spineHasCupCapAtoms_spine
            (cellHasCupCapGenerators_ofAdjunctionSignature
              (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta)))
      have proxyConditions : MatchingSwapStateConditions 0
          { openWires := [], links := [], nextFresh := 1, loops := 0 } :=
        { bottomLe := Nat.zero_le 1
          forest := by exact True.intro
          nfPos := Nat.lt_succ_self 0
          fresh := ⟨fun _ absurdMem => (by cases absurdMem),
            fun _ absurdMem => (by cases absurdMem)⟩ }
      have proxyExtractsEqual : extractDiagram 0
          (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
            cellAlphaFirst.spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              cellAlphaSecond.spine) :=
        (shiftAlphaFirst.symm.trans extractsEqual).trans shiftAlphaSecond
      have proxyComposite := extractAfterProcessing_vcompLeft_ofSeed cellBeta 0
        { openWires := [], links := [], nextFresh := 1, loops := 0 }
        proxyConditions zeroLength.symm
        (cellHasCupCapGenerators_ofAdjunctionSignature cellAlphaSecond)
        (cellHasCupCapGenerators_ofAdjunctionSignature cellBeta)
        proxyExtractsEqual
      exact (shiftCompositeFirst.trans proxyComposite).trans shiftCompositeSecond.symm

/-! ## Honesty marker -/

/-- **Honesty marker — the vcomp-LEFT matching congruence is SHIPPED.**  The run-composition
law (`spine_vcomp` + `processSpine_append`), the seed-generic core chaining reconstruction →
fold → forward extraction, and the walking-adjunction field inhabitant with both boundary
legs (canonical seed / counter-shift proxy).  NOT yet covered: the vcomp-RIGHT congruence
(its premise lives at cellBeta's own canonical seed while the composite runs cellBeta from
the post-α state — needs the action-factors-through-the-diagram leg) and the two whisker
fields (boundary-padding compositionality) — the remaining MODE3-C bricks.  `= true`. -/
def fxMode_hasMatchingVcompLeftCongruence : Bool := true

end FX1Poly.Polygraph
