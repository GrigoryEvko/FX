import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescRegionTransportKit

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescDispatchResidualsAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gates in the per-file twins) over every headline declaration of the three dispatch-residual bricks —
the J-loop engine lemma (`WiringDescLoopBubbleEngine`), the J-geometry ordered rewrite (`WiringDescStraddleSinkOrdered`),
and the J-transport reshape kit (`WiringDescRegionTransportKit`).  Each must print "does not depend on any axioms".
Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- J-loop (WiringDescLoopBubbleEngine)
#print axioms FX1Poly.Polygraph.loopBubbleProcessLoops
#print axioms FX1Poly.Polygraph.loopBubbleLoopsEqOne
#print axioms FX1Poly.Polygraph.loopBubbleNotEmpty
#print axioms FX1Poly.Polygraph.outcomeLoopAtFactoredTotal
#print axioms FX1Poly.Polygraph.fxBrauer_loopBubbleEngineTerminalState

-- J-geometry (WiringDescStraddleSinkOrdered)
#print axioms FX1Poly.Polygraph.swapCrossingPastDistantStep
#print axioms FX1Poly.Polygraph.commuteSettledCrossingPastTail
#print axioms FX1Poly.Polygraph.regionArrivedExact_ofPeelSnoc
#print axioms FX1Poly.Polygraph.sinkDistantThenStraddle_arrives
#print axioms FX1Poly.Polygraph.sinkDistantThenStraddle_arrivesWitness
#print axioms FX1Poly.Polygraph.fxBrauer_straddleSinkOrderedTerminalState

-- J-transport (WiringDescRegionTransportKit)
#print axioms FX1Poly.Polygraph.RegionCupOutcome.transportByRegionEq
#print axioms FX1Poly.Polygraph.crossingWiring_reconstruct
#print axioms FX1Poly.Polygraph.crossingAtom_reconstruct
#print axioms FX1Poly.Polygraph.transportCrossingHead
#print axioms FX1Poly.Polygraph.transportByRegionEq_fate
#print axioms FX1Poly.Polygraph.fxBrauer_regionTransportKitTerminalState

end FX1PolyAudit
