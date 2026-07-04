import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPartitionSimStep
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcWindowCommutation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshBlockTransposition

/-! # WalkingAdjunction/ArcCapCapSwapCore — the CAP x CAP two-step partition-simulation core

The FOURTH two-step swap combo, in the corrected vehicle.  Both cap-cap obstructions
(`ArcCapCapSwapObstruction`, `ArcCapCapAgreeObstruction`) showed the renaming and plain-agreement
vehicles fail here; the target is `ArcPartitionSim` under the EVENT TRANSPOSITION
`arcFreshBlockTransposition state.nextFresh 1 1` (the swap `nf <-> nf + 1` of the two cap event
nodes, fixing everything else).

This file opens the core with the WIRE leg: the two run orders produce the SAME open-wire list
(`natListRemoveTwoAt_removeAbove_commute` — removing the high pair first and then the low pair
equals removing low-first and then at the down-shifted position), and the transposition fixes
every remaining wire (wires are OLD nodes, strictly below `nextFresh`), so the `openMap` field
holds with the map degenerating to the identity. -/

namespace FX1Poly.Polygraph

/-- ★ **The cap-cap `openMap` leg.**  HIGH-first wires (`removeTwoAt` at `gap + 2 + positionLow`
then at `positionLow`) equal the `sigma`-image of LOW-first wires (`removeTwoAt` at
`positionLow` then at `gap + positionLow`): the raw lists agree by the unconditional
remove-remove commutation, and the event transposition fixes every surviving wire
(`arcFreshBlockTransposition_ofBelow` on the freshness bound, through two `removeTwoAt`
membership projections). -/
theorem capCapSwap_openMap (state : ArcWireState) (positionLow gap : Nat)
    (wiresFresh : ∀ wire ∈ state.openWires, wire < state.nextFresh) :
    (stepCapArc (stepCapArc state (gap + 2 + positionLow)) positionLow).openWires
      = ((stepCapArc (stepCapArc state positionLow) (gap + positionLow)).openWires).map
          (arcFreshBlockTransposition state.nextFresh 1 1) := by
  show natListRemoveTwoAt (natListRemoveTwoAt state.openWires (gap + 2 + positionLow))
        positionLow
     = (natListRemoveTwoAt (natListRemoveTwoAt state.openWires positionLow)
         (gap + positionLow)).map (arcFreshBlockTransposition state.nextFresh 1 1)
  rw [natListRemoveTwoAt_removeAbove_commute state.openWires positionLow gap,
    mapFixedOn (arcFreshBlockTransposition state.nextFresh 1 1)
      (natListRemoveTwoAt (natListRemoveTwoAt state.openWires positionLow) (gap + positionLow))
      (fun wire wireMember =>
        arcFreshBlockTransposition_ofBelow state.nextFresh 1 1 wire
          (wiresFresh wire
            (mem_natListRemoveTwoAt state.openWires positionLow wire
              (mem_natListRemoveTwoAt
                (natListRemoveTwoAt state.openWires positionLow)
                (gap + positionLow) wire wireMember))))]

/-- **Honesty marker — the cap-cap core's WIRE leg is BUILT.**  `capCapSwap_openMap` discharges
the `openMap` field of the target `ArcPartitionSim (arcFreshBlockTransposition state.nextFresh
1 1)` instance between the two cap-cap run orders (`nfEq` and the event-LIST equalities are
definitional: both orders allocate `nf` then `nf + 1` and cons them in the same order).  What
this marker does NOT claim: the `componentsCorr` leg (disjoint-merge join-commutation + the
event swap), the `loopsEq` leg (the rank argument over the four wire reads), the two count
legs, and the assembled core instance.  `= true` records the wire leg only. -/
def fxMode_hasCapCapSwapWireLeg : Bool := true

end FX1Poly.Polygraph
