import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCountRename
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLinksAsEvents
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCountRestricted
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingMidNodeAgreement

/-! # MatchingMidLoopAgreement — equal loop increments over the mid-state links (MODE3-D)

The LOOP-leg glue: the four shipped engines compose into the loop-increment equality the
composite runs need.  The additive exchange decomposition
(`countJoinEventLoops_overLinks_exchange`) rewrites each renamed trace's count over the mid
links into its empty-base count plus the mid edges' count over its own fold; the empty-base
counts agree through the rename invariance (`countJoinEventLoops_ofRename`) and the canonical
loop read-offs; the mid-edge counts agree through the restricted congruence
(`countJoinEventLoops_congrOnNodeSet`) at the below-base node set, whose view hypothesis is
the below-base fold agreement (`belowBaseFoldView_agrees_ofViewSim`); a hand-rolled left
cancellation (the core right-cancellation leaks `propext`) closes.

★ `countJoinEventLoops_overMidLinks_agrees_ofViewSim` — the LOOP-leg headline, hypothesis
shape aligned with the VIEW leg's `compositeBoundaryView_agrees_ofExtractEq` bundle for the
run-level unpacking.  Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Hand-rolled left cancellation (the core right-cancellation lemma leaks `propext`). -/
private theorem natAddLeftCancel : (leftAddend firstNumber secondNumber : Nat) →
    leftAddend + firstNumber = leftAddend + secondNumber → firstNumber = secondNumber
  | 0, firstNumber, secondNumber, sumsEqual => by
      rw [Nat.zero_add, Nat.zero_add] at sumsEqual
      exact sumsEqual
  | leftAddend + 1, firstNumber, secondNumber, sumsEqual => by
      rw [Nat.succ_add, Nat.succ_add] at sumsEqual
      exact natAddLeftCancel leftAddend firstNumber secondNumber (Nat.succ.inj sumsEqual)

/-- ★ **The two renamed traces close equally many loops over the mid-state links.**  Exchange
both counts into empty-base form, transport the canonical loop equality through the rename
invariance, close the mid-edge counts by the restricted congruence at the below-base node
set, and cancel the shared mid-links self-count. -/
theorem countJoinEventLoops_overMidLinks_agrees_ofViewSim (wires : List Nat) (freshBase : Nat)
    (discipline : RelativeWireZoneDiscipline wires freshBase)
    (bottomCount : Nat) (midTracks : wires.length = bottomCount)
    (stateA stateB : WireState) (eventsA eventsB midLinks : List (Nat × Nat))
    (linksA : stateA.links = applyJoinEvents eventsA [])
    (linksB : stateB.links = applyJoinEvents eventsB [])
    (loopsA : stateA.loops = countJoinEventLoops eventsA [])
    (loopsB : stateB.loops = countJoinEventLoops eventsB [])
    (viewSim : MatchingConnectivityViewSim bottomCount stateA stateB)
    (midForest : isUnionFindForest midLinks)
    (baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midLinks →
      leftNode < freshBase ∧ rightNode < freshBase) :
    countJoinEventLoops (eventsA.map (fun event =>
        (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2)))
      midLinks
      = countJoinEventLoops (eventsB.map (fun event =>
          (relativeWireMap wires freshBase event.1,
            relativeWireMap wires freshBase event.2)))
        midLinks := by
  have canonicalCountsEqual : countJoinEventLoops eventsA []
      = countJoinEventLoops eventsB [] :=
    (loopsA.symm.trans viewSim.loopsEq).trans loopsB
  have renamedCountsEqual : countJoinEventLoops (eventsA.map (fun event =>
      (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2))) []
      = countJoinEventLoops (eventsB.map (fun event =>
        (relativeWireMap wires freshBase event.1,
          relativeWireMap wires freshBase event.2))) [] := by
    rw [countJoinEventLoops_ofRename (relativeWireMap wires freshBase)
        discipline.isInjective eventsA,
      countJoinEventLoops_ofRename (relativeWireMap wires freshBase)
        discipline.isInjective eventsB]
    exact canonicalCountsEqual
  have midCountsEqual : countJoinEventLoops midLinks
      (applyJoinEvents (eventsA.map (fun event =>
        (relativeWireMap wires freshBase event.1,
          relativeWireMap wires freshBase event.2))) [])
      = countJoinEventLoops midLinks
        (applyJoinEvents (eventsB.map (fun event =>
          (relativeWireMap wires freshBase event.1,
            relativeWireMap wires freshBase event.2))) []) :=
    countJoinEventLoops_congrOnNodeSet (fun node => node < freshBase) midLinks
      (applyJoinEvents (eventsA.map (fun event =>
        (relativeWireMap wires freshBase event.1,
          relativeWireMap wires freshBase event.2))) [])
      (applyJoinEvents (eventsB.map (fun event =>
        (relativeWireMap wires freshBase event.1,
          relativeWireMap wires freshBase event.2))) [])
      (isUnionFindForest_applyJoinEvents _ [] True.intro)
      (isUnionFindForest_applyJoinEvents _ [] True.intro)
      (fun pair membership => baseBounded pair.1 pair.2 membership)
      (fun probeOne probeTwo oneBelow twoBelow =>
        belowBaseFoldView_agrees_ofViewSim wires freshBase discipline bottomCount midTracks
          stateA stateB eventsA eventsB linksA linksB viewSim probeOne probeTwo
          oneBelow twoBelow)
  apply natAddLeftCancel (countJoinEventLoops midLinks [])
  rw [countJoinEventLoops_overLinks_exchange (eventsA.map (fun event =>
      (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2)))
      midLinks midForest,
    countJoinEventLoops_overLinks_exchange (eventsB.map (fun event =>
      (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2)))
      midLinks midForest,
    renamedCountsEqual, midCountsEqual]

/-- **Honesty marker — the LOOP leg of the interface gluing is PROVED at the event level.**
Equal canonical loop counts and an extract-level connectivity-view simulation force the two
renamed second-half traces to close equally many loops over the mid-state links.  NOT yet
shipped: the SAT-D5 run-level premise unpacking (the composite runs' loops/links/wires read
off through the D4a kinematics into this statement and the VIEW leg's). -/
def fxMode_hasMidLinksLoopAgreement : Bool := true

end FX1Poly.Polygraph
