import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCompositeExtract
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompLeftCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWireDistinct
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeZone

/-! # mode-3 — the vcomp-RIGHT matching congruence (MODE3-D, SAT-D6, the positive-mid leg)

The Joyal–Street leg: two cells with equal matchings stay matching-equal after PRE-composing
any third cell.  Unlike the LEFT congruence (whose premise transports through the composite
fold), the RIGHT premise lives at cellBeta's OWN canonical seed while the composite runs
cellBeta from the post-α mid-state — the relative-run extract agreement
(`processSpine_extract_eq_ofCanonicalExtractEq`) is exactly the bridge, and this file supplies
its mid-state provenance:

  * ★ `extractAfterProcessing_vcompRight_ofSeed` — the seed-generic core: the composite runs
    split over append, the conditions package + distinctness invariant + zone discipline ride
    the α-fold to the shared mid-state, the window-suffix invariant reads off the mid boundary
    width, and the relative extract agreement lands the composite extract equality;
  * ★ `matchingOf_vcompRight_congruence_ofMidBoundaryPos` — the walking-adjunction inhabitant
    for an inhabited MID boundary, source-boundary-dispatched (canonical seed when the source
    boundary is inhabited, the MODE3-B counter-shift proxy when it is empty — the premise is
    untouched by the source-side exchange because it lives at the mid seed).

NOT covered here (honesty): the empty-MID-boundary leg (`oneCellG.length = 0`) — there the
canonical β-runs start at the DEGENERATE seed where the loop read-off's positivity guard
fails; its engine (the proxy-detour loop-count read-off + the fresh-zone-only relative run)
is the next brick, after which the unconditional headline closes SAT-D6.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Nat + range plumbing (hand-rolled private copies; core equivalents leak propext) -/

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

/-! ## The seed-generic core -/

/-- ★ **The seed-generic vcomp-RIGHT extract congruence (inhabited mid boundary).**  The
composite runs split over append (`spine_vcomp` + `processSpine_append`); the conditions
package (`matchingSwapStateConditions_processSpine`), the distinctness invariant
(`processSpine_wireListDistinct`), and the zone discipline
(`relativeWireZoneDiscipline_ofState`) ride the α-fold to the shared mid-state; the
window-suffix invariant reads off the mid boundary width; and the relative extract agreement
(`processSpine_extract_eq_ofCanonicalExtractEq`) turns the β-cells' equal canonical extracts
into the composite extract equality. -/
theorem extractAfterProcessing_vcompRight_ofSeed {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    {cellBetaFirst cellBetaSecond : RawTwoCellExpr signature oneCellG oneCellH}
    (bottomCount : Nat) (seed : WireState)
    (seedConditions : MatchingSwapStateConditions bottomCount seed)
    (seedTracks : seed.openWires.length = oneCellF.length)
    (seedDistinct : WireListDistinct seed.openWires)
    (alphaCupCap : CellHasCupCapGenerators cellAlpha)
    (betaFirstCupCap : CellHasCupCapGenerators cellBetaFirst)
    (betaSecondCupCap : CellHasCupCapGenerators cellBetaSecond)
    (midBoundaryPos : 0 < oneCellG.length)
    (extractsEqual : extractDiagram oneCellG.length
        (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaFirst.spine)
      = extractDiagram oneCellG.length
          (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaSecond.spine)) :
    extractDiagram bottomCount
        (processSpine seed (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine)
      = extractDiagram bottomCount
          (processSpine seed (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine) := by
  rw [RawTwoCellExpr.spine_vcomp cellAlpha cellBetaFirst,
    RawTwoCellExpr.spine_vcomp cellAlpha cellBetaSecond,
    processSpine_append cellAlpha.spine cellBetaFirst.spine seed,
    processSpine_append cellAlpha.spine cellBetaSecond.spine seed]
  have midConditions : MatchingSwapStateConditions bottomCount
      (processSpine seed cellAlpha.spine) :=
    matchingSwapStateConditions_processSpine bottomCount cellAlpha.spine seed seedConditions
  have midDistinct : WireListDistinct (processSpine seed cellAlpha.spine).openWires :=
    processSpine_wireListDistinct cellAlpha.spine seed seedConditions.fresh
      seedConditions.nfPos seedDistinct
  have midDiscipline : RelativeWireZoneDiscipline
      (processSpine seed cellAlpha.spine).openWires
      (processSpine seed cellAlpha.spine).nextFresh :=
    relativeWireZoneDiscipline_ofState (processSpine seed cellAlpha.spine)
      midConditions.fresh midDistinct
  have windowInRange : (identityPath sourceMode).length + oneCellF.length
      ≤ seed.openWires.length := by
    show 0 + oneCellF.length ≤ seed.openWires.length
    rw [Nat.zero_add]
    exact Nat.le_of_eq seedTracks.symm
  have suffixInvariant := (runMatchingCell_openWiresSuffix_invariant
    (identityPath sourceMode) (identityPath targetMode) cellAlpha seed
    alphaCupCap windowInRange).2
  have midTracks : (processSpine seed cellAlpha.spine).openWires.length
      = oneCellG.length := by
    have lengthBalance : (processSpine seed cellAlpha.spine).openWires.length
        + oneCellF.length = seed.openWires.length + oneCellG.length := suffixInvariant
    rw [seedTracks, Nat.add_comm oneCellF.length oneCellG.length] at lengthBalance
    exact natAddRightCancel oneCellF.length lengthBalance
  exact processSpine_extract_eq_ofCanonicalExtractEq bottomCount oneCellG.length
    (processSpine seed cellAlpha.spine) cellBetaFirst.spine cellBetaSecond.spine
    cellBetaFirst.spineBoundaryChained_spine
    (cellBetaFirst.spineHasCupCapAtoms_spine betaFirstCupCap)
    cellBetaSecond.spineBoundaryChained_spine
    (cellBetaSecond.spineHasCupCapAtoms_spine betaSecondCupCap)
    midTracks midBoundaryPos midConditions.fresh midConditions.nfPos midConditions.forest
    midDiscipline midConditions.bottomLe extractsEqual

/-! ## The walking-adjunction inhabitant (inhabited mid boundary) -/

/-- ★ **The vcomp-RIGHT matching congruence at the walking adjunction, inhabited MID
boundary** — source-boundary-dispatched between the canonical seed (the initial conditions
package applies) and the MODE3-B counter-shift proxy `⟨[], [], 1, 0⟩` (empty source boundary —
the degenerate seed is exchanged on the two composite runs; the β-premise lives at the mid
seed and is untouched by the exchange). -/
theorem matchingOf_vcompRight_congruence_ofMidBoundaryPos
    {sourceMode targetMode : AdjunctionMode}
    {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG)
    {cellBetaFirst cellBetaSecond : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH}
    (midBoundaryPos : 0 < oneCellG.length)
    (matchingsEqual : matchingOf cellBetaFirst = matchingOf cellBetaSecond) :
    matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst)
      = matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond) := by
  show extractDiagram oneCellF.length
      (processSpine (canonicalMatchingSeed oneCellF.length)
        (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine)
    = extractDiagram oneCellF.length
        (processSpine (canonicalMatchingSeed oneCellF.length)
          (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine)
  have extractsEqual : extractDiagram oneCellG.length
      (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaFirst.spine)
    = extractDiagram oneCellG.length
        (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaSecond.spine) :=
    matchingsEqual
  cases Nat.lt_or_ge 0 oneCellF.length with
  | inl sourceInhabited =>
      exact extractAfterProcessing_vcompRight_ofSeed cellAlpha oneCellF.length
        (canonicalMatchingSeed oneCellF.length)
        (matchingSwapStateConditions_initial oneCellF.length sourceInhabited)
        (rangeLength oneCellF.length)
        (canonicalMatchingSeed_wireListDistinct oneCellF.length)
        (cellHasCupCapGenerators_ofAdjunctionSignature cellAlpha)
        (cellHasCupCapGenerators_ofAdjunctionSignature cellBetaFirst)
        (cellHasCupCapGenerators_ofAdjunctionSignature cellBetaSecond)
        midBoundaryPos extractsEqual
  | inr sourceAtMostZero =>
      have zeroLength : oneCellF.length = 0 :=
        Nat.le_antisymm sourceAtMostZero (Nat.zero_le oneCellF.length)
      rw [zeroLength]
      have shiftCompositeFirst : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine) :=
        extractAfterProcessing_emptyBoundary_counterShift
          (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine
          (zeroLength ▸ (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spineBoundaryChained_spine)
          ((RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spineHasCupCapAtoms_spine
            (cellHasCupCapGenerators_ofAdjunctionSignature
              (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst)))
      have shiftCompositeSecond : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine) :=
        extractAfterProcessing_emptyBoundary_counterShift
          (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine
          (zeroLength ▸ (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spineBoundaryChained_spine)
          ((RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spineHasCupCapAtoms_spine
            (cellHasCupCapGenerators_ofAdjunctionSignature
              (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond)))
      have proxyConditions : MatchingSwapStateConditions 0
          { openWires := [], links := [], nextFresh := 1, loops := 0 } :=
        { bottomLe := Nat.zero_le 1
          forest := by exact True.intro
          nfPos := Nat.lt_succ_self 0
          fresh := ⟨fun _ absurdMem => (by cases absurdMem),
            fun _ absurdMem => (by cases absurdMem)⟩ }
      have proxyDistinct : WireListDistinct ([] : List Nat) :=
        fun _ _ _ twoInRange => nomatch twoInRange
      have proxyComposite := extractAfterProcessing_vcompRight_ofSeed cellAlpha 0
        { openWires := [], links := [], nextFresh := 1, loops := 0 }
        proxyConditions zeroLength.symm proxyDistinct
        (cellHasCupCapGenerators_ofAdjunctionSignature cellAlpha)
        (cellHasCupCapGenerators_ofAdjunctionSignature cellBetaFirst)
        (cellHasCupCapGenerators_ofAdjunctionSignature cellBetaSecond)
        midBoundaryPos extractsEqual
      exact (shiftCompositeFirst.trans proxyComposite).trans shiftCompositeSecond.symm

/-! ## Honesty marker -/

/-- **Honesty marker — the vcomp-RIGHT matching congruence is SHIPPED for inhabited MID
boundaries.**  The seed-generic core rides the conditions package, the distinctness
invariant, and the zone discipline through the α-fold into the relative extract agreement;
the walking-adjunction inhabitant dispatches both source-boundary legs.  NOT yet shipped:
the empty-MID-boundary leg (the degenerate mid seed's loop read-off via the proxy detour +
the fresh-zone-only relative run) and with it the unconditional headline — the remaining
SAT-D6 brick.  `= true`. -/
def fxMode_hasMatchingVcompRightCongruenceOnPositiveMidBoundary : Bool := true

end FX1Poly.Polygraph
