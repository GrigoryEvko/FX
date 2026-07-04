import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # ArcPositionalShiftSim — the positional two-run correspondence for the head cancellation

The head-cancellation residual (peel campaign H) compares TWO arc folds of the SAME atom list:
the composite run continuing from the state the peeled head left behind, and the tail's own
fresh run at the head's target boundary.  Their positional legs — open wires, the allocation
counter, the cup/cap event lists — evolve INDEPENDENTLY of the links (only the passive loop
counter reads them), so they correspond under a fixed id-reindexing `sigma` that translates by
`delta` above the base run's allocation frontier: wires are pointwise `sigma`-images, the
shifted counter stays `delta` ahead, and the shifted event lists are `sigma`-mapped base lists
over the head's own event suffix.  Cup/cap steps preserve the correspondence unconditionally
(no windows, no chainedness, no forests — `natListInsertAt_map` / `natListRemoveTwoAt_map` are
unconditional), so it folds over any walking-adjunction spine.

The LINKS leg — the composite components as the base components with the head's leg-join
transported through the fold — is deliberately NOT here; it is the next rung, consuming this
one.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The positional shift simulation.**  `shiftedState` runs `delta` ids ahead of `baseState`
under the reindexing `sigma`: open wires are pointwise `sigma`-images, the allocation counter
is `delta` ahead, the base counter sits at or above `threshold` (the zone where `sigma` is the
plain `+ delta` translation), and each event list is the `sigma`-mapped base list over a fixed
head-event suffix. -/
structure ArcPositionalShiftSim (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat)
    (baseState shiftedState : ArcWireState) : Prop where
  /-- The open wires are pointwise `sigma`-images. -/
  openMap : shiftedState.openWires = baseState.openWires.map sigma
  /-- The shifted allocation counter stays `delta` ahead. -/
  nfShift : shiftedState.nextFresh = baseState.nextFresh + delta
  /-- The base counter never falls below the translation zone's floor. -/
  nfFloor : threshold ≤ baseState.nextFresh
  /-- The shifted cup events are the `sigma`-mapped base ones over the head's suffix. -/
  cupEventsMap : shiftedState.cupEventNodes
    = baseState.cupEventNodes.map sigma ++ headCupEvents
  /-- The shifted cap events are the `sigma`-mapped base ones over the head's suffix. -/
  capEventsMap : shiftedState.capEventNodes
    = baseState.capEventNodes.map sigma ++ headCapEvents

/-- The simulated runs keep equal boundary lengths (`sigma`-mapping preserves length). -/
theorem arcPositionalShiftSim_openWiresLength (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat) (baseState shiftedState : ArcWireState)
    (sim : ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState) :
    shiftedState.openWires.length = baseState.openWires.length := by
  rw [sim.openMap]
  exact mapLength sigma baseState.openWires

/-- **A cup step preserves the positional shift simulation.**  Both runs splice their two fresh
legs at the same position; the base legs sit above the floor, so `sigma` translates them onto
the shifted legs, and `natListInsertAt_map` commutes the splice with the mapping. -/
theorem arcPositionalShiftSim_stepCupArc (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat) (baseState shiftedState : ArcWireState)
    (position : Nat)
    (sigmaShiftsAboveThreshold : ∀ identifier, threshold ≤ identifier →
      sigma identifier = identifier + delta)
    (sim : ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState) :
    ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      (stepCupArc baseState position) (stepCupArc shiftedState position) where
  openMap := by
    have legZeroShifts : sigma baseState.nextFresh = baseState.nextFresh + delta :=
      sigmaShiftsAboveThreshold baseState.nextFresh sim.nfFloor
    have legOneShifts : sigma (baseState.nextFresh + 1) = baseState.nextFresh + 1 + delta :=
      sigmaShiftsAboveThreshold (baseState.nextFresh + 1)
        (Nat.le_trans sim.nfFloor (Nat.le_add_right baseState.nextFresh 1))
    show natListInsertAt shiftedState.openWires position
        [shiftedState.nextFresh, shiftedState.nextFresh + 1]
      = (natListInsertAt baseState.openWires position
          [baseState.nextFresh, baseState.nextFresh + 1]).map sigma
    rw [natListInsertAt_map sigma baseState.openWires position
      [baseState.nextFresh, baseState.nextFresh + 1]]
    show natListInsertAt shiftedState.openWires position
        [shiftedState.nextFresh, shiftedState.nextFresh + 1]
      = natListInsertAt (baseState.openWires.map sigma) position
          [sigma baseState.nextFresh, sigma (baseState.nextFresh + 1)]
    rw [sim.openMap, sim.nfShift, legZeroShifts, legOneShifts,
      Nat.add_right_comm baseState.nextFresh 1 delta]
  nfShift := by
    show shiftedState.nextFresh + 3 = baseState.nextFresh + 3 + delta
    rw [sim.nfShift, Nat.add_right_comm baseState.nextFresh delta 3]
  nfFloor := Nat.le_trans sim.nfFloor (Nat.le_add_right baseState.nextFresh 3)
  cupEventsMap := by
    have eventShifts : sigma (baseState.nextFresh + 2) = baseState.nextFresh + 2 + delta :=
      sigmaShiftsAboveThreshold (baseState.nextFresh + 2)
        (Nat.le_trans sim.nfFloor (Nat.le_add_right baseState.nextFresh 2))
    show (shiftedState.nextFresh + 2) :: shiftedState.cupEventNodes
      = sigma (baseState.nextFresh + 2) :: (baseState.cupEventNodes.map sigma ++ headCupEvents)
    rw [sim.nfShift, sim.cupEventsMap, eventShifts,
      Nat.add_right_comm baseState.nextFresh 2 delta]
  capEventsMap := sim.capEventsMap

/-- **A cap step preserves the positional shift simulation.**  Both runs drop the two wires at
the same position (`natListRemoveTwoAt_map` commutes the drop with the mapping) and record one
event at their respective counters, which correspond by the translation. -/
theorem arcPositionalShiftSim_stepCapArc (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat) (baseState shiftedState : ArcWireState)
    (position : Nat)
    (sigmaShiftsAboveThreshold : ∀ identifier, threshold ≤ identifier →
      sigma identifier = identifier + delta)
    (sim : ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState) :
    ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      (stepCapArc baseState position) (stepCapArc shiftedState position) where
  openMap := by
    show natListRemoveTwoAt shiftedState.openWires position
      = (natListRemoveTwoAt baseState.openWires position).map sigma
    rw [natListRemoveTwoAt_map sigma baseState.openWires position, sim.openMap]
  nfShift := by
    show shiftedState.nextFresh + 1 = baseState.nextFresh + 1 + delta
    rw [sim.nfShift, Nat.add_right_comm baseState.nextFresh delta 1]
  nfFloor := Nat.le_trans sim.nfFloor (Nat.le_add_right baseState.nextFresh 1)
  cupEventsMap := sim.cupEventsMap
  capEventsMap := by
    have eventShifts : sigma baseState.nextFresh = baseState.nextFresh + delta :=
      sigmaShiftsAboveThreshold baseState.nextFresh sim.nfFloor
    show shiftedState.nextFresh :: shiftedState.capEventNodes
      = sigma baseState.nextFresh :: (baseState.capEventNodes.map sigma ++ headCapEvents)
    rw [sim.nfShift, sim.capEventsMap, eventShifts]

/-- One cup/cap-arity atom preserves the positional shift simulation — both runs fire the SAME
atom, so the window position agrees and the arity dispatch picks the branch. -/
theorem arcPositionalShiftSim_stepArcAtom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat) (baseState shiftedState : ArcWireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (sigmaShiftsAboveThreshold : ∀ identifier, threshold ≤ identifier →
      sigma identifier = identifier + delta)
    (sim : ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState) :
    ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      (stepArcAtom baseState atom) (stepArcAtom shiftedState atom) := by
  cases arity with
  | inl cupArity =>
      rw [stepArcAtom_eq_stepCupArc baseState atom cupArity.1 cupArity.2,
        stepArcAtom_eq_stepCupArc shiftedState atom cupArity.1 cupArity.2]
      exact arcPositionalShiftSim_stepCupArc sigma delta threshold headCupEvents headCapEvents
        baseState shiftedState atom.leftContext.length sigmaShiftsAboveThreshold sim
  | inr capArity =>
      rw [stepArcAtom_eq_stepCapArc baseState atom capArity.1 capArity.2,
        stepArcAtom_eq_stepCapArc shiftedState atom capArity.1 capArity.2]
      exact arcPositionalShiftSim_stepCapArc sigma delta threshold headCupEvents headCapEvents
        baseState shiftedState atom.leftContext.length sigmaShiftsAboveThreshold sim

/-- ★ **The positional shift simulation folds over every walking-adjunction spine** — every
adjunction atom is cup- or cap-arity, and each step preserves the correspondence with no side
conditions, so no chainedness or freshness threading is needed. -/
theorem arcPositionalShiftSim_processArcSpine
    {overallSource overallTarget : adjunctionGraph.Mode}
    (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat)
    (sigmaShiftsAboveThreshold : ∀ identifier, threshold ≤ identifier →
      sigma identifier = identifier + delta) :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (baseState shiftedState : ArcWireState) →
    ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState →
    ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      (processArcSpine baseState atoms) (processArcSpine shiftedState atoms)
  | [], _, _, sim => sim
  | headAtom :: restAtoms, baseState, shiftedState, sim => by
      show ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
        (processArcSpine (stepArcAtom baseState headAtom) restAtoms)
        (processArcSpine (stepArcAtom shiftedState headAtom) restAtoms)
      exact arcPositionalShiftSim_processArcSpine sigma delta threshold
        headCupEvents headCapEvents sigmaShiftsAboveThreshold restAtoms
        (stepArcAtom baseState headAtom) (stepArcAtom shiftedState headAtom)
        (arcPositionalShiftSim_stepArcAtom sigma delta threshold headCupEvents headCapEvents
          baseState shiftedState headAtom
          (adjunctionSpineAtom_hasCupOrCapArity headAtom) sigmaShiftsAboveThreshold sim)

/-! ## Honesty marker -/

/-- **Honesty marker — the POSITIONAL leg of the head-cancellation simulation is SHIPPED (peel
campaign H, rung 1).**  `ArcPositionalShiftSim` (wires as `sigma`-images, allocator `delta`
ahead, event lists `sigma`-mapped over head suffixes), preserved unconditionally by cup and cap
steps, dispatched per atom, folded over every walking-adjunction spine.  What this marker does
NOT claim: the LINKS/component leg (the head's leg-join transported through the fold — the H2
core), the explicit head reindex at the concrete seed pair, and the extract correspondence they
assemble into.  `= true`. -/
def fxMode_hasArcPositionalShiftSim : Bool := true

end FX1Poly.Polygraph
