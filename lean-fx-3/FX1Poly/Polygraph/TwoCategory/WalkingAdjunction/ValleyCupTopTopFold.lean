import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupTopTopStepTransport
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupSpine

/-! # ValleyCupTopTopFold — the two-floor peel induction of the top-top offset agreement (Piece II tail)

The per-step engine `topRegionOffsetAgrees_step` (`ValleyCupTopTopStepTransport`) proves that ONE shared
top-of-stack cup step preserves the two-floor top-region offset-space agreement.  This file FOLDS that engine
across a whole pure-cup boundary-chained block, at TWO floors simultaneously — `floorHi` (the whole valley,
`bottomCount`) and `floorLo` (the cup alone, `midWidth`) — carried as a single cons-induction.

## Why cons induction (not reverse/peel-last)

The transport `diagramPartner_stepCupArc` rewrites `partner(stepCupArc state w)` in terms of `partner(state)`.
Cons induction on the cup block processes the FIRST cup onto each seed and recurses on the tail with the STEPPED
seed pair.  The invariant carried IN is the seed-pair agreement `topRegionOffsetAgrees floorHi floorLo
(partner stateHi) (partner stateLo) (openWires)`; each cons step promotes it to the stepped-seed agreement by
`topRegionOffsetAgrees_step` (after rewriting the two partners by `diagramPartner_stepCupArc`), then recurses.
At the empty block the carried seed agreement IS the conclusion.  No reverse-induction machinery, no snoc.

## The per-seed invariant thread

`diagramPartner_stepCupArc` needs, at each seed, `ArcStateFresh` / `isUnionFindForest` / `seedBoundary ≤
nextFresh` / `ArcBoundaryCensus` / `windowFits`.  All five propagate through `stepCupArc` by the shipped
`arcStateFresh_stepCupArc` / `isUnionFindForest_stepCupArc` / (`nextFresh + 3`, defeq) /
`arcBoundaryCensus_stepCupArc`, and the next window fits because the chaining pins each cup's dom boundary to the
running open-wire count (`stepArcAtom_openWires_tracksBoundary` + `spineBoundaryChained_tail`).  Both runs share
each cup's window (a syntactic `leftContext.length`), and both open-wire counts stay equal (each cup adds two).

## What this file lands (zero-axiom) — and the residual it does NOT discharge

  * ★ `topRegionOffsetAgrees_fold` — the two-floor peel induction: from a seed-pair agreement over `openWires`,
    the whole cup block's two runs agree over the final open-wire count.

This is the "induction itself" the `ValleyCupTopTopStepTransport` header names.  What remains for
`cupTopTopPartner` (`ValleyCupReconstruct`, cup case 3): the base-case seed reconciliation (the two concrete
seeds `capState` and `arcInit midWidth` agree OFF the top-top ports — their survivor tops are all tag-false), and
the WireState ↔ arc bridge (`arcDiagram_eq_matching` at both floors + the `capState` promotion into the arc
encoding).  No gate flag is flipped; fib-3 also carries the independent Piece-I beam
(`MatchingReductsShareSpineTrace`, #1996).

Raw Lean 4 + Init; structural recursion over the cup block, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local plumbing (propext-free copies) -/

private theorem rangeLoopLenFold : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLenFold count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLenFold (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLenFold count []]
  exact Nat.add_zero count

/-- A top-of-stack cup adds exactly two open wires (defeq to `natListInsertAt_length`). -/
private theorem stepCupArc_openWiresLenFold (state : ArcWireState) (position : Nat) :
    (stepCupArc state position).openWires.length = state.openWires.length + 2 :=
  natListInsertAt_length state.openWires position [state.nextFresh, state.nextFresh + 1]

/-- The extracted partner list has length `floor + openWires`. -/
private theorem extractArcPartnerLenFold (floor : Nat) (state : ArcWireState) :
    (extractArc floor state).diagram.partner.length = floor + state.openWires.length := by
  show ((List.range (floor + state.openWires.length)).map
      (partnerIndexOf state.links (List.range floor ++ state.openWires)
        (floor + state.openWires.length))).length = floor + state.openWires.length
  rw [mapLength, rangeLenFold]

/-! ## The two-floor peel induction -/

/-- ★ **The two-floor peel induction of the top-top offset agreement.**  From a seed-pair agreement over the
seed open-wire region, processing the SAME pure-cup boundary-chained block through BOTH runs (floors `floorHi` /
`floorLo`) preserves the top-region offset-space agreement, over the final open-wire count.  Cons induction on
the block: each cup promotes the seed agreement by `topRegionOffsetAgrees_step` (both partners rewritten by
`diagramPartner_stepCupArc`), threading the per-seed `ArcStateFresh` / `isUnionFindForest` / `seedBelowFresh` /
`ArcBoundaryCensus` invariants and the shared window fit; the base returns the carried agreement. -/
theorem topRegionOffsetAgrees_fold {overallSource overallTarget : adjunctionGraph.Mode}
    (floorHi floorLo : Nat) :
    (cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    AllCupArity cupBlock →
    (stateHi stateLo : ArcWireState) →
    ArcStateFresh stateHi → isUnionFindForest stateHi.links →
      floorHi ≤ stateHi.nextFresh → ArcBoundaryCensus floorHi stateHi →
    ArcStateFresh stateLo → isUnionFindForest stateLo.links →
      floorLo ≤ stateLo.nextFresh → ArcBoundaryCensus floorLo stateLo →
    SpineBoundaryChained stateHi.openWires.length cupBlock →
    SpineBoundaryChained stateLo.openWires.length cupBlock →
    stateHi.openWires.length = stateLo.openWires.length →
    topRegionOffsetAgrees floorHi floorLo
        (extractArc floorHi stateHi).diagram.partner
        (extractArc floorLo stateLo).diagram.partner
        stateHi.openWires.length →
    topRegionOffsetAgrees floorHi floorLo
        (extractArc floorHi (processArcSpine stateHi cupBlock)).diagram.partner
        (extractArc floorLo (processArcSpine stateLo cupBlock)).diagram.partner
        (processArcSpine stateHi cupBlock).openWires.length
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, seedAgree => seedAgree
  | firstCup :: rest, cupPure, stateHi, stateLo,
      freshHi, forestHi, seedBelowHi, censusHi,
      freshLo, forestLo, seedBelowLo, censusLo,
      chainedHi, chainedLo, openWiresEq, seedAgree => by
    -- the head is a cup; peel its arity and the tail's purity
    cases cupPure with
    | cons hasCupDomArity hasCupCodArity restPure =>
      -- the shared window is the head's left-context width
      have stepEqHi : stepArcAtom stateHi firstCup = stepCupArc stateHi firstCup.leftContext.length :=
        stepArcAtom_eq_stepCupArc stateHi firstCup hasCupDomArity hasCupCodArity
      have stepEqLo : stepArcAtom stateLo firstCup = stepCupArc stateLo firstCup.leftContext.length :=
        stepArcAtom_eq_stepCupArc stateLo firstCup hasCupDomArity hasCupCodArity
      -- chaining pins the head's dom boundary to the running open-wire count
      obtain ⟨headFiresHi, chainedRestHi⟩ := spineBoundaryChained_tail chainedHi
      obtain ⟨_, chainedRestLo⟩ := spineBoundaryChained_tail chainedLo
      have windowFitsHi : firstCup.leftContext.length ≤ stateHi.openWires.length := by
        rw [← headFiresHi]
        show firstCup.leftContext.length
          ≤ firstCup.leftContext.length + firstCup.generatorDom.length + firstCup.rightContext.length
        exact Nat.le_trans (Nat.le_add_right firstCup.leftContext.length firstCup.generatorDom.length)
          (Nat.le_add_right _ firstCup.rightContext.length)
      have windowFitsLo : firstCup.leftContext.length ≤ stateLo.openWires.length := openWiresEq ▸ windowFitsHi
      -- length facts feeding the step lemma
      have lenHi : (extractArc floorHi stateHi).diagram.partner.length = floorHi + stateHi.openWires.length :=
        extractArcPartnerLenFold floorHi stateHi
      have lenLo : (extractArc floorLo stateLo).diagram.partner.length = floorLo + stateHi.openWires.length := by
        rw [extractArcPartnerLenFold floorLo stateLo, openWiresEq]
      -- promote the seed agreement across the head cup, at both floors
      have steppedAgree : topRegionOffsetAgrees floorHi floorLo
          (extractArc floorHi (stepCupArc stateHi firstCup.leftContext.length)).diagram.partner
          (extractArc floorLo (stepCupArc stateLo firstCup.leftContext.length)).diagram.partner
          (stepCupArc stateHi firstCup.leftContext.length).openWires.length := by
        rw [diagramPartner_stepCupArc floorHi stateHi firstCup.leftContext.length
              freshHi forestHi seedBelowHi censusHi windowFitsHi,
            diagramPartner_stepCupArc floorLo stateLo firstCup.leftContext.length
              freshLo forestLo seedBelowLo censusLo windowFitsLo,
            stepCupArc_openWiresLenFold stateHi firstCup.leftContext.length]
        exact topRegionOffsetAgrees_step floorHi floorLo firstCup.leftContext.length stateHi.openWires.length
          (extractArc floorHi stateHi).diagram.partner (extractArc floorLo stateLo).diagram.partner
          lenHi lenLo windowFitsHi seedAgree
      -- propagate the per-seed invariants through the head cup
      have freshHi' : ArcStateFresh (stepCupArc stateHi firstCup.leftContext.length) :=
        arcStateFresh_stepCupArc stateHi firstCup.leftContext.length freshHi
      have forestHi' : isUnionFindForest (stepCupArc stateHi firstCup.leftContext.length).links :=
        isUnionFindForest_stepCupArc stateHi firstCup.leftContext.length forestHi
      have seedBelowHi' : floorHi ≤ (stepCupArc stateHi firstCup.leftContext.length).nextFresh := by
        show floorHi ≤ stateHi.nextFresh + 3
        exact Nat.le_trans seedBelowHi (Nat.le_add_right stateHi.nextFresh 3)
      have censusHi' : ArcBoundaryCensus floorHi (stepCupArc stateHi firstCup.leftContext.length) :=
        arcBoundaryCensus_stepCupArc floorHi stateHi firstCup.leftContext.length
          freshHi forestHi seedBelowHi windowFitsHi censusHi
      have freshLo' : ArcStateFresh (stepCupArc stateLo firstCup.leftContext.length) :=
        arcStateFresh_stepCupArc stateLo firstCup.leftContext.length freshLo
      have forestLo' : isUnionFindForest (stepCupArc stateLo firstCup.leftContext.length).links :=
        isUnionFindForest_stepCupArc stateLo firstCup.leftContext.length forestLo
      have seedBelowLo' : floorLo ≤ (stepCupArc stateLo firstCup.leftContext.length).nextFresh := by
        show floorLo ≤ stateLo.nextFresh + 3
        exact Nat.le_trans seedBelowLo (Nat.le_add_right stateLo.nextFresh 3)
      have censusLo' : ArcBoundaryCensus floorLo (stepCupArc stateLo firstCup.leftContext.length) :=
        arcBoundaryCensus_stepCupArc floorLo stateLo firstCup.leftContext.length
          freshLo forestLo seedBelowLo windowFitsLo censusLo
      -- transport the tail chaining to the stepped open-wire counts
      have boundaryEqHi : (stepCupArc stateHi firstCup.leftContext.length).openWires.length
          = firstCup.codBoundaryLength := by
        rw [← stepEqHi]
        exact stepArcAtom_openWires_tracksBoundary stateHi firstCup
          (Or.inl ⟨hasCupDomArity, hasCupCodArity⟩) headFiresHi.symm
      have chainedRestHi' : SpineBoundaryChained
          (stepCupArc stateHi firstCup.leftContext.length).openWires.length rest := by
        rw [boundaryEqHi]; exact chainedRestHi
      have boundaryEqLo : (stepCupArc stateLo firstCup.leftContext.length).openWires.length
          = firstCup.codBoundaryLength := by
        rw [← stepEqLo]
        exact stepArcAtom_openWires_tracksBoundary stateLo firstCup
          (Or.inl ⟨hasCupDomArity, hasCupCodArity⟩) (openWiresEq ▸ headFiresHi.symm)
      have chainedRestLo' : SpineBoundaryChained
          (stepCupArc stateLo firstCup.leftContext.length).openWires.length rest := by
        rw [boundaryEqLo]; exact chainedRestLo
      -- both stepped open-wire counts stay equal (each cup adds two)
      have openWiresEq' : (stepCupArc stateHi firstCup.leftContext.length).openWires.length
          = (stepCupArc stateLo firstCup.leftContext.length).openWires.length := by
        rw [stepCupArc_openWiresLenFold stateHi firstCup.leftContext.length,
          stepCupArc_openWiresLenFold stateLo firstCup.leftContext.length, openWiresEq]
      -- recurse on the tail with the stepped seed pair
      have recResult := topRegionOffsetAgrees_fold floorHi floorLo rest restPure
        (stepCupArc stateHi firstCup.leftContext.length) (stepCupArc stateLo firstCup.leftContext.length)
        freshHi' forestHi' seedBelowHi' censusHi' freshLo' forestLo' seedBelowLo' censusLo'
        chainedRestHi' chainedRestLo' openWiresEq' steppedAgree
      -- the whole-block run IS the tail run onto the stepped seed
      show topRegionOffsetAgrees floorHi floorLo
          (extractArc floorHi (processArcSpine (stepArcAtom stateHi firstCup) rest)).diagram.partner
          (extractArc floorLo (processArcSpine (stepArcAtom stateLo firstCup) rest)).diagram.partner
          (processArcSpine (stepArcAtom stateHi firstCup) rest).openWires.length
      rw [stepEqHi, stepEqLo]
      exact recResult

/-! ## Honesty marker -/

/-- **Honesty marker — the two-floor peel induction of the top-top offset agreement is LANDED.**

Landed here, zero-axiom:

  * `topRegionOffsetAgrees_fold` — the two-floor peel induction: from a seed-pair top-region offset agreement,
    the same pure-cup boundary-chained block's two runs (floors `floorHi` / `floorLo`) agree over the final
    open-wire count.  Cons induction folds `topRegionOffsetAgrees_step` across the block, threading the per-seed
    `ArcStateFresh` / `isUnionFindForest` / `seedBelowFresh` / `ArcBoundaryCensus` invariants and the shared
    window fit; the base returns the carried agreement.

This is the "induction itself" the `ValleyCupTopTopStepTransport` header names as the un-shipped residual.  What
remains for `cupTopTopPartner` (`ValleyCupReconstruct`, cup case 3), hence `cupRestrict_reconstructs` (which keeps
it as a hypothesis) and downstream `valleyAppend_split` / `valleysWithEqualMatching_spineTraceEquiv`: (i) the
base-case seed reconciliation (the two concrete seeds `capState` / `arcInit midWidth` agree OFF the top-top
ports); (ii) the WireState ↔ arc bridge (`arcDiagram_eq_matching` at both floors + the `capState` arc promotion).
No gate flag is flipped; fib-3 also carries the independent Piece-I beam (`MatchingReductsShareSpineTrace`,
#1996).  `= true`. -/
def fxMode_hasCupTopTopFold : Bool := true

end FX1Poly.Polygraph
