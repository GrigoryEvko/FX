import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcMatchViewBridge
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingViewSimulation

/-! # ArcMatchViewFold — the diagram = matching bridge (the fold consuming the per-step peel)

The per-step event-node peel (`ArcMatchViewBridge`) says a single cup/cap arc step, projected via
`arcToWire`, shares the boundary same-component view of the corresponding matching step.  This file threads
that peel through a whole boundary-disciplined spine and lands the **diagram = matching bridge**:

  `(arcStructureOfSpineList bottomCount atoms).diagram = matchingOfSpineList bottomCount atoms`.

Architecture, bottom-up:

  * `matchingConnectivityViewSim_trans` — the view simulation composes (missing transitivity of
    `MatchingConnectivityViewSim`).
  * `matchingSwapStateConditions_arcToWire` — the arc-side freshness/forest invariants supply the matching
    conditions package on the projected `WireState` (needed to feed the shipped per-atom matching dispatch).
  * `arcMatchViewSim_stepCupPeel` / `arcMatchViewSim_stepCapPeel` — the peel lemmas lifted from raw
    `isSameComponent` to `matchingSameComponent`, using the tight post-step boundary-node bound (a cup's
    post-step nodes sit below `nextFresh + 2`, a cap's below `nextFresh`).
  * `arcMatchViewSim_stepArcAtom` — one atom: `simA` (peel, arc step vs matching step of the same projection)
    composed with `simB` (the shipped matching per-atom dispatch carrying the incoming view to `matchState`).
  * `arcMatchConnectivityViewSim_processArcSpine` — the fold, threading `ArcStateFresh`/forest/seed-bound on
    the arc side and `MatchingSwapStateConditions` on the matching side, exactly as the census fold does.
  * ★ `arcDiagram_eq_matching` — the assembled bridge, via `extractDiagram_eq_of_connectivityView` at the
    seed (`arcToWire` of the initial arc state IS the initial matching state).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

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

/-! ## Transitivity of the connectivity-view simulation -/

/-- **The connectivity-view simulation composes.**  Lengths and loops chain by `Eq.trans`; the view agreement
carries because the middle state's open-wire count matches the last's, so an in-range index for the last is
in-range for the middle. -/
theorem matchingConnectivityViewSim_trans (bottomCount : Nat) (stateA stateB stateC : WireState)
    (simAB : MatchingConnectivityViewSim bottomCount stateA stateB)
    (simBC : MatchingConnectivityViewSim bottomCount stateB stateC) :
    MatchingConnectivityViewSim bottomCount stateA stateC where
  lengthEq := simAB.lengthEq.trans simBC.lengthEq
  loopsEq := simAB.loopsEq.trans simBC.loopsEq
  viewAgrees := by
    intro firstIndex secondIndex firstInRange secondInRange
    have firstInMiddle : firstIndex < bottomCount + stateB.openWires.length := by
      rw [simBC.lengthEq]; exact firstInRange
    have secondInMiddle : secondIndex < bottomCount + stateB.openWires.length := by
      rw [simBC.lengthEq]; exact secondInRange
    exact (simAB.viewAgrees firstIndex secondIndex firstInMiddle secondInMiddle).trans
      (simBC.viewAgrees firstIndex secondIndex firstInRange secondInRange)

/-! ## The arc-side invariants supply the matching conditions package -/

/-- **The arc freshness/forest invariants give the matching conditions package on the projection.**  `arcToWire`
keeps `openWires`/`links`/`nextFresh` verbatim, so `WireStateFresh (arcToWire state)` is the first two conjuncts
of `ArcStateFresh state`, and the boundary/forest/positivity conditions transfer directly. -/
theorem matchingSwapStateConditions_arcToWire (bottomCount : Nat) (arcState : ArcWireState)
    (fresh : ArcStateFresh arcState) (forest : isUnionFindForest arcState.links)
    (bottomLe : bottomCount ≤ arcState.nextFresh) (nfPos : 0 < arcState.nextFresh) :
    MatchingSwapStateConditions bottomCount (arcToWire arcState) where
  bottomLe := bottomLe
  forest := forest
  nfPos := nfPos
  fresh := ⟨fresh.1, fresh.2.1⟩

/-! ## The per-step peel lifted to `matchingSameComponent` (simA) -/

/-- **The cup peel at the view level.**  A cup arc step and the matching cup step of the same projection share
open wires and loops, and their boundary same-component views agree because every post-step boundary node sits
strictly below `nextFresh + 2` — the tight bound the raw peel `isSameComponent_stepCupArc_eq_stepCup` consumes. -/
theorem arcMatchViewSim_stepCupPeel (bottomCount : Nat) (arcState : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh arcState) (forest : isUnionFindForest arcState.links)
    (bottomLe : bottomCount ≤ arcState.nextFresh) :
    MatchingConnectivityViewSim bottomCount (arcToWire (stepCupArc arcState position))
      (stepCup (arcToWire arcState) position) where
  lengthEq := rfl
  loopsEq := rfl
  viewAgrees := by
    intro firstIndex secondIndex _firstInRange _secondInRange
    have boundEach : ∀ node ∈ (List.range bottomCount
        ++ natListInsertAt arcState.openWires position [arcState.nextFresh, arcState.nextFresh + 1]),
        node < arcState.nextFresh + 2 := by
      apply mem_append_lt (arcState.nextFresh + 2) (List.range bottomCount)
        (natListInsertAt arcState.openWires position [arcState.nextFresh, arcState.nextFresh + 1])
      · intro node nodeInRange
        exact Nat.lt_trans (Nat.lt_of_lt_of_le (mem_range_imp_lt nodeInRange) bottomLe)
          (Nat.lt_add_of_pos_right (by decide))
      · apply natListInsertAt_all_lt (arcState.nextFresh + 2) arcState.openWires position
          [arcState.nextFresh, arcState.nextFresh + 1]
        · intro node nodeInOpen
          exact Nat.lt_trans (fresh.1 node nodeInOpen) (Nat.lt_add_of_pos_right (by decide))
        · intro node nodeInBlock
          cases nodeInBlock with
          | head => exact Nat.lt_add_of_pos_right (by decide)
          | tail _ nodeInTail =>
              cases nodeInTail with
              | head => exact Nat.add_lt_add_left (by decide) arcState.nextFresh
              | tail _ nodeInNil => cases nodeInNil
    have posBound : (0 : Nat) < arcState.nextFresh + 2 :=
      Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 2 arcState.nextFresh)
    exact isSameComponent_stepCupArc_eq_stepCup arcState position fresh forest
      (natListGetAt (List.range bottomCount
        ++ natListInsertAt arcState.openWires position [arcState.nextFresh, arcState.nextFresh + 1]) firstIndex)
      (natListGetAt (List.range bottomCount
        ++ natListInsertAt arcState.openWires position [arcState.nextFresh, arcState.nextFresh + 1]) secondIndex)
      (natListGetAt_lt (arcState.nextFresh + 2) posBound _ firstIndex boundEach)
      (natListGetAt_lt (arcState.nextFresh + 2) posBound _ secondIndex boundEach)

/-- **The cap peel at the view level.**  A cap arc step and the matching cap step of the same projection share
open wires (both drop the same two, `stepCap_openWires` collapsing the matching cap's branch) and loops (same
same-component increment), and their boundary views agree because every post-step boundary node sits strictly
below `nextFresh` — the bound the raw peel `isSameComponent_stepCapArc_eq_stepCap` consumes. -/
theorem arcMatchViewSim_stepCapPeel (bottomCount : Nat) (arcState : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh arcState) (forest : isUnionFindForest arcState.links)
    (bottomLe : bottomCount ≤ arcState.nextFresh) (nfPos : 0 < arcState.nextFresh) :
    MatchingConnectivityViewSim bottomCount (arcToWire (stepCapArc arcState position))
      (stepCap (arcToWire arcState) position) where
  lengthEq := by
    show (natListRemoveTwoAt arcState.openWires position).length
      = (stepCap (arcToWire arcState) position).openWires.length
    rw [stepCap_openWires (arcToWire arcState) position]
    rfl
  loopsEq := by
    show (stepCapArc arcState position).loops = (stepCap (arcToWire arcState) position).loops
    rw [stepCap_loops (arcToWire arcState) position]
    dsimp only [stepCapArc, arcToWire]
    rfl
  viewAgrees := by
    intro firstIndex secondIndex _firstInRange _secondInRange
    have boundEach : ∀ node ∈ (List.range bottomCount ++ natListRemoveTwoAt arcState.openWires position),
        node < arcState.nextFresh := by
      apply mem_append_lt arcState.nextFresh (List.range bottomCount)
        (natListRemoveTwoAt arcState.openWires position)
      · intro node nodeInRange
        exact Nat.lt_of_lt_of_le (mem_range_imp_lt nodeInRange) bottomLe
      · exact natListRemoveTwoAt_all_lt arcState.nextFresh arcState.openWires position fresh.1
    dsimp only [matchingSameComponent, matchingBoundaryNodes]
    rw [stepCap_openWires (arcToWire arcState) position]
    exact isSameComponent_stepCapArc_eq_stepCap arcState position fresh forest
      (natListGetAt (List.range bottomCount ++ natListRemoveTwoAt arcState.openWires position) firstIndex)
      (natListGetAt (List.range bottomCount ++ natListRemoveTwoAt arcState.openWires position) secondIndex)
      (natListGetAt_lt arcState.nextFresh nfPos _ firstIndex boundEach)
      (natListGetAt_lt arcState.nextFresh nfPos _ secondIndex boundEach)

/-! ## The combined per-atom step (simA ∘ simB) -/

/-- **One boundary-tracked cup/cap atom carries the arc/matching view simulation.**  `simA` is the peel (the
arc step versus the matching step of the SAME projection), `simB` is the shipped matching per-atom dispatch
carrying the incoming view from the projection to `matchState`; their composite bridges the arc step to the
matching step. -/
theorem arcMatchViewSim_stepArcAtom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (arcState : ArcWireState) (matchState : WireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (fresh : ArcStateFresh arcState) (forest : isUnionFindForest arcState.links)
    (bottomLe : bottomCount ≤ arcState.nextFresh) (nfPos : 0 < arcState.nextFresh)
    (conditions : MatchingSwapStateConditions bottomCount matchState)
    (arity : AtomHasCupOrCapArity atom)
    (tracksEntry : arcState.openWires.length = atom.domBoundaryLength)
    (sim : MatchingConnectivityViewSim bottomCount (arcToWire arcState) matchState) :
    MatchingConnectivityViewSim bottomCount (arcToWire (stepArcAtom arcState atom)) (stepAtom matchState atom) := by
  have conditionsArc : MatchingSwapStateConditions bottomCount (arcToWire arcState) :=
    matchingSwapStateConditions_arcToWire bottomCount arcState fresh forest bottomLe nfPos
  have tracksMatch : matchState.openWires.length = atom.domBoundaryLength :=
    sim.lengthEq.symm.trans tracksEntry
  have simB : MatchingConnectivityViewSim bottomCount (stepAtom (arcToWire arcState) atom)
      (stepAtom matchState atom) :=
    matchingConnectivityViewSim_stepAtom bottomCount matchState (arcToWire arcState) atom
      conditions conditionsArc arity tracksMatch sim
  have simA : MatchingConnectivityViewSim bottomCount (arcToWire (stepArcAtom arcState atom))
      (stepAtom (arcToWire arcState) atom) := by
    cases arity with
    | inl cupArity =>
        rw [stepArcAtom_eq_stepCupArc arcState atom cupArity.1 cupArity.2,
          stepAtom_ofCupArity (arcToWire arcState) atom cupArity.1 cupArity.2]
        exact arcMatchViewSim_stepCupPeel bottomCount arcState atom.leftContext.length fresh forest bottomLe
    | inr capArity =>
        rw [stepArcAtom_eq_stepCapArc arcState atom capArity.1 capArity.2,
          stepAtom_ofCapArity (arcToWire arcState) atom capArity.1 capArity.2]
        exact arcMatchViewSim_stepCapPeel bottomCount arcState atom.leftContext.length fresh forest bottomLe nfPos
  exact matchingConnectivityViewSim_trans bottomCount (arcToWire (stepArcAtom arcState atom))
    (stepAtom (arcToWire arcState) atom) (stepAtom matchState atom) simA simB

/-! ## The fold and the assembled bridge -/

/-- **The whole boundary-disciplined spine carries the arc/matching view simulation.**  Threads `ArcStateFresh`
/ forest / seed-bound / positivity on the arc side and `MatchingSwapStateConditions` on the matching side,
exactly as the census fold, dispatching each atom onto `arcMatchViewSim_stepArcAtom`. -/
theorem arcMatchConnectivityViewSim_processArcSpine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) →
    (arcState : ArcWireState) → (matchState : WireState) → (boundaryLength : Nat) →
    ArcStateFresh arcState → isUnionFindForest arcState.links →
    bottomCount ≤ arcState.nextFresh → 0 < arcState.nextFresh →
    MatchingSwapStateConditions bottomCount matchState →
    SpineHasCupCapAtoms atoms →
    SpineBoundaryChained boundaryLength atoms →
    arcState.openWires.length = boundaryLength →
    MatchingConnectivityViewSim bottomCount (arcToWire arcState) matchState →
    MatchingConnectivityViewSim bottomCount (arcToWire (processArcSpine arcState atoms))
      (processSpine matchState atoms)
  | [], _, _, _, _, _, _, _, _, _, _, _, sim => sim
  | atom :: rest, arcState, matchState, _, fresh, forest, bottomLe, nfPos, conditions, arity, chained,
      tracks, sim => by
    obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
    obtain ⟨headArity, tailArity⟩ := spineHasCupCapAtoms_tail arity
    have tracksEntry : arcState.openWires.length = atom.domBoundaryLength := tracks.trans headFires.symm
    exact arcMatchConnectivityViewSim_processArcSpine bottomCount rest
      (stepArcAtom arcState atom) (stepAtom matchState atom) atom.codBoundaryLength
      (arcStateFresh_stepArcAtom arcState atom fresh)
      (isUnionFindForest_stepArcAtom_ofCupOrCap arcState atom headArity forest)
      (Nat.le_trans bottomLe (stepArcAtom_nextFresh_le arcState atom))
      (Nat.lt_of_lt_of_le nfPos (stepArcAtom_nextFresh_le arcState atom))
      (matchingSwapStateConditions_stepAtom bottomCount matchState atom conditions)
      tailArity tailChained
      (stepArcAtom_openWires_tracksBoundary arcState atom headArity tracksEntry)
      (arcMatchViewSim_stepArcAtom bottomCount arcState matchState atom fresh forest bottomLe nfPos
        conditions headArity tracksEntry sim)

/-- ★ **The diagram = matching bridge.**  For any boundary-disciplined cup/cap spine (a non-empty bottom
boundary), the arc structure's boundary `.diagram` field IS the matching-route `DiagramType`: the arc run's
projection and the matching run share the boundary-connectivity view at every reachable state (the fold above,
seeded at the shared initial state — `arcToWire` of the initial arc state is literally the initial matching
state), so their `extractDiagram` reads coincide (`extractDiagram_eq_of_connectivityView`). -/
theorem arcDiagram_eq_matching {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode))
    (arity : SpineHasCupCapAtoms atoms) (chained : SpineBoundaryChained bottomCount atoms)
    (bottomPos : 0 < bottomCount) :
    (arcStructureOfSpineList bottomCount atoms).diagram = matchingOfSpineList bottomCount atoms := by
  have sim : MatchingConnectivityViewSim bottomCount
      (arcToWire (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms))
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ atoms) :=
    arcMatchConnectivityViewSim_processArcSpine bottomCount atoms
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      ⟨List.range bottomCount, [], bottomCount, 0⟩ bottomCount
      (arcStateFresh_initial bottomCount) isUnionFindForest_nil (Nat.le_refl bottomCount) bottomPos
      (matchingSwapStateConditions_initial bottomCount bottomPos)
      arity chained (rangeLength bottomCount)
      (matchingConnectivityViewSim_refl bottomCount ⟨List.range bottomCount, [], bottomCount, 0⟩)
  have firstLen := sim.lengthEq
  have relAgrees : ∀ firstIndex secondIndex,
      firstIndex < bottomCount
        + (arcToWire (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            atoms)).openWires.length →
      secondIndex < bottomCount
        + (arcToWire (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            atoms)).openWires.length →
      matchingSameComponent bottomCount
          (arcToWire (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms))
          firstIndex secondIndex
        = matchingSameComponent bottomCount
          (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ atoms) firstIndex secondIndex := by
    intro firstIndex secondIndex firstInRange secondInRange
    exact sim.viewAgrees firstIndex secondIndex (firstLen ▸ firstInRange) (firstLen ▸ secondInRange)
  exact extractDiagram_eq_of_connectivityView bottomCount
    (arcToWire (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms))
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ atoms)
    sim.lengthEq sim.loopsEq relAgrees

/-! ## Honesty marker -/

/-- **Honesty marker — the diagram = matching bridge is SHIPPED.**  The view simulation composes
(`matchingConnectivityViewSim_trans`), the arc invariants supply the matching conditions package
(`matchingSwapStateConditions_arcToWire`), the per-step peel lifts to `matchingSameComponent` under the tight
post-step boundary-node bound (`arcMatchViewSim_stepCupPeel` / `...CapPeel`), one atom bridges via simA ∘ simB
(`arcMatchViewSim_stepArcAtom`), the fold threads it end-to-end
(`arcMatchConnectivityViewSim_processArcSpine`), and the seed assembles the bridge
(`arcDiagram_eq_matching` : `(arcStructureOfSpineList bc l).diagram = matchingOfSpineList bc l`).  What this
does NOT claim: the internal cup/cap count reconstruction and the assembled Piece II.  `= true`. -/
def fxMode_hasArcMatchDiagramBridge : Bool := true

end FX1Poly.Polygraph
