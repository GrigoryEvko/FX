import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # WalkingAdjunction/ArcPartitionSimulation — the sigma-twisted partition simulation

The UNIFIED swap vehicle the two cap-cap obstructions pin down.  The renaming vehicle
(`ArcStepSimCount`) fails on cap-cap because old-node REPRESENTATIVES diverge; the plain
agreement vehicle (`ArcStateAgree`) fails because EVENT attachments swap.  What survives both
fixtures is the `sigma`-twisted PARTITION simulation:

  * `componentsCorr` — `isSameComponent stateT.links (sigma x) (sigma y) = isSameComponent
    stateS.links x y` — replaces the root-level `rootComm`: it never mentions a representative;
  * `cupCountCorr` / `capCountCorr` — per-PROBE, PORT-ROOTED event counts (`countEventsInRoot
    links (rootOf links probe) events`) replace the per-root-VALUE counts: the count is keyed by
    the probe's own component, so the divergent representative cancels.

This relation is strictly weaker than `ArcStepSimCount` — `arcPartitionSim_of_arcStepSimCount`
derives it from `rootComm` + injectivity, so the three SHIPPED heterogeneous two-step
simulations (CUP x CUP / CUP x CAP / CAP x CUP) transport into it by a three-line bridge — and
it is still strong enough for the extract: `sameArcPartition_of_arcPartitionSim` reads out
`SameArcPartition`, hence equal arc extracts.  The cap-cap instance (under the event
transposition `sigma`) and the step-stability of this relation are the remaining bricks; this
file ships the interface, the bridge, and the readout. -/

namespace FX1Poly.Polygraph

/-- ★ **The `sigma`-twisted partition simulation** — the unified, representative-free swap
invariant.  Open wires are pointwise `sigma`-images, counters and loops agree, the same-component
relation corresponds under `sigma` (NO root-level commutation), and the per-probe port-rooted
cup/cap event counts correspond.  Satisfiable for ALL FOUR two-step swap combos: derivable from
`ArcStepSimCount` on the three heterogeneous ones, and directly satisfiable (with `sigma` the
event transposition) at both cap-cap obstruction fixtures where the stronger vehicles fail. -/
structure ArcPartitionSim (sigma : Nat → Nat) (stateS stateT : ArcWireState) : Prop where
  /-- The open wires are pointwise `sigma`-images. -/
  openMap : stateT.openWires = stateS.openWires.map sigma
  /-- The fresh-allocation counters agree. -/
  nfEq : stateS.nextFresh = stateT.nextFresh
  /-- The loop counts agree. -/
  loopsEq : stateT.loops = stateS.loops
  /-- The same-component relation corresponds under `sigma` — the partition-level replacement
  for the (cap-cap-refuted) root-level `rootComm`. -/
  componentsCorr : ∀ probeLeft probeRight,
      isSameComponent stateT.links (sigma probeLeft) (sigma probeRight)
        = isSameComponent stateS.links probeLeft probeRight
  /-- The cup-event count in the `sigma`-image probe's OWN component matches the probe's — keyed
  by the probe, never by a representative value. -/
  cupCountCorr : ∀ probe,
      countEventsInRoot stateT.links (unionFindRootOf stateT.links (sigma probe))
          stateT.cupEventNodes
        = countEventsInRoot stateS.links (unionFindRootOf stateS.links probe)
          stateS.cupEventNodes
  /-- The cap-event count in the `sigma`-image probe's OWN component matches the probe's. -/
  capCountCorr : ∀ probe,
      countEventsInRoot stateT.links (unionFindRootOf stateT.links (sigma probe))
          stateT.capEventNodes
        = countEventsInRoot stateS.links (unionFindRootOf stateS.links probe)
          stateS.capEventNodes
  /-- The first link list is a forest. -/
  forestS : isUnionFindForest stateS.links
  /-- The second link list is a forest. -/
  forestT : isUnionFindForest stateT.links

/-- ★ **The bridge: every renaming simulation is a partition simulation.**  `componentsCorr` is
`rootComm` twice plus injectivity of `sigma` on the `==`; the count fields are the per-root
counts instantiated at the probe's OWN root, transported along `rootComm`.  Through this bridge
the three SHIPPED heterogeneous two-step swaps (`arcStepSimCount_cupCupSwap` /
`arcStepSimCount_cupCapSwap` / `arcStepSimCount_capCupSwap`) all land in the unified vehicle. -/
theorem arcPartitionSim_of_arcStepSimCount (sigma : Nat → Nat)
    (inj : ∀ leftPreimage rightPreimage,
      sigma leftPreimage = sigma rightPreimage → leftPreimage = rightPreimage)
    (stateS stateT : ArcWireState) (sim : ArcStepSimCount sigma stateS stateT) :
    ArcPartitionSim sigma stateS stateT where
  openMap := sim.openMap
  nfEq := sim.nfEq
  loopsEq := sim.loopsEq
  componentsCorr := by
    intro probeLeft probeRight
    show (unionFindRootOf stateT.links (sigma probeLeft)
            == unionFindRootOf stateT.links (sigma probeRight))
       = (unionFindRootOf stateS.links probeLeft == unionFindRootOf stateS.links probeRight)
    rw [sim.rootComm probeLeft, sim.rootComm probeRight, beq_congr_inj sigma inj]
  cupCountCorr := by
    intro probe
    rw [sim.rootComm probe]
    exact sim.cupCorr (unionFindRootOf stateS.links probe)
  capCountCorr := by
    intro probe
    rw [sim.rootComm probe]
    exact sim.capCorr (unionFindRootOf stateS.links probe)
  forestS := sim.forestS
  forestT := sim.forestT

/-- ★ **Partition-simulated states share the partition view** — the readout to
`SameArcPartition`.  The boundary nodes of `stateT` are the `sigma`-images of `stateS`'s
(`openMap` on the wire block, `fixesBoundary` on the bottom-port block), so every boundary
same-component boolean transports along `componentsCorr` and every per-port event count along
the per-probe count fields.  No injectivity and no root value is consumed anywhere. -/
theorem sameArcPartition_of_arcPartitionSim (bottomCount : Nat) (sigma : Nat → Nat)
    (sigmaFixesZero : sigma 0 = 0)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (stateS stateT : ArcWireState) (sim : ArcPartitionSim sigma stateS stateT) :
    SameArcPartition bottomCount stateS stateT := by
  have boundaryMap : boundaryNodesOf bottomCount stateT
      = (boundaryNodesOf bottomCount stateS).map sigma := by
    show List.range bottomCount ++ stateT.openWires
       = (List.range bottomCount ++ stateS.openWires).map sigma
    rw [sim.openMap, mapAppend, mapFixedOn sigma (List.range bottomCount)
      (fun identifier identifierInRange => fixesBoundary identifier
        (mem_range_imp_lt identifierInRange))]
  have lengthsEq : stateT.openWires.length = stateS.openWires.length := by
    rw [sim.openMap, mapLength]
  refine ⟨lengthsEq.symm, sim.loopsEq.symm, ?_, ?_, ?_⟩
  · intro firstIndex secondIndex _ _
    show (unionFindRootOf stateS.links
            (natListGetAt (boundaryNodesOf bottomCount stateS) firstIndex)
          == unionFindRootOf stateS.links
            (natListGetAt (boundaryNodesOf bottomCount stateS) secondIndex))
       = (unionFindRootOf stateT.links
            (natListGetAt (boundaryNodesOf bottomCount stateT) firstIndex)
          == unionFindRootOf stateT.links
            (natListGetAt (boundaryNodesOf bottomCount stateT) secondIndex))
    rw [boundaryMap, natListGetAt_map sigma sigmaFixesZero, natListGetAt_map sigma sigmaFixesZero]
    exact (sim.componentsCorr
      (natListGetAt (boundaryNodesOf bottomCount stateS) firstIndex)
      (natListGetAt (boundaryNodesOf bottomCount stateS) secondIndex)).symm
  · intro index _
    show countEventsInRoot stateS.links
        (unionFindRootOf stateS.links (natListGetAt (boundaryNodesOf bottomCount stateS) index))
        stateS.cupEventNodes
      = countEventsInRoot stateT.links
        (unionFindRootOf stateT.links (natListGetAt (boundaryNodesOf bottomCount stateT) index))
        stateT.cupEventNodes
    rw [boundaryMap, natListGetAt_map sigma sigmaFixesZero]
    exact (sim.cupCountCorr (natListGetAt (boundaryNodesOf bottomCount stateS) index)).symm
  · intro index _
    show countEventsInRoot stateS.links
        (unionFindRootOf stateS.links (natListGetAt (boundaryNodesOf bottomCount stateS) index))
        stateS.capEventNodes
      = countEventsInRoot stateT.links
        (unionFindRootOf stateT.links (natListGetAt (boundaryNodesOf bottomCount stateT) index))
        stateT.capEventNodes
    rw [boundaryMap, natListGetAt_map sigma sigmaFixesZero]
    exact (sim.capCountCorr (natListGetAt (boundaryNodesOf bottomCount stateS) index)).symm

/-- ★ **Partition-simulated states have EQUAL arc extracts** — with the (order-independent,
separately-discharged) event-list length agreements, via `extractArc_eq_of_sameArcPartition`. -/
theorem extractArc_eq_of_arcPartitionSim (bottomCount : Nat) (sigma : Nat → Nat)
    (sigmaFixesZero : sigma 0 = 0)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (stateS stateT : ArcWireState) (sim : ArcPartitionSim sigma stateS stateT)
    (cupLengthsAgree : stateS.cupEventNodes.length = stateT.cupEventNodes.length)
    (capLengthsAgree : stateS.capEventNodes.length = stateT.capEventNodes.length) :
    extractArc bottomCount stateS = extractArc bottomCount stateT :=
  extractArc_eq_of_sameArcPartition bottomCount stateS stateT
    (sameArcPartition_of_arcPartitionSim bottomCount sigma sigmaFixesZero fixesBoundary
      stateS stateT sim)
    cupLengthsAgree capLengthsAgree

/-- **Honesty marker — the unified partition-simulation INTERFACE is BUILT.**  `ArcPartitionSim`
is derivable from `ArcStepSimCount` (`arcPartitionSim_of_arcStepSimCount` — the three shipped
heterogeneous swaps transport in) and reads out to `SameArcPartition` / equal extracts.  What
this marker does NOT claim: (a) step-stability of `ArcPartitionSim` through a common suffix (the
per-probe count fields through a cap merge — the next substrate brick), and (b) the cap-cap
CORE instance under the event transposition (openMap with wire-fixing `sigma`, remove-remove
commutation, partition join-commutation, the loop rank argument).  `= true` records the
interface, the bridge, and the readout only. -/
def fxMode_hasArcPartitionSimInterface : Bool := true

end FX1Poly.Polygraph
