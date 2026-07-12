import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExt5CorrectedRoundtripBridge

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescExt5CorrectedRoundtripBridgeAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER r54 R3-A roundtrip
bridge: the marker-bridge, the census bridge and its payoff, the tranche fired on the entangled / with-cap witnesses,
the `bottomCount = 0` residual pins, the content marker, and the machine-checked terminal state.  Each must print
"does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_ofPos
#print axioms FX1Poly.Polygraph.isBoundaryInvolution_ofValidCensus
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_ofValidCensus
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_monster
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_monster_viaCensus
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_adversarialB
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_wildCapThrough
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_wildCrossThrough
#print axioms FX1Poly.Polygraph.nestedCups_bottomCount_zero
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_nestedCups_decide
#print axioms FX1Poly.Polygraph.fxBrauer_hasExt5CorrectedRoundtripPosBottom
#print axioms FX1Poly.Polygraph.fxBrauer_ext5CorrectedRoundtripBridgeTerminalState

end FX1PolyAudit
