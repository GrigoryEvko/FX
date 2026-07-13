import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescClosedDiagramRoundtripClose

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescClosedDiagramRoundtripCloseAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER r55 closed-diagram
roundtrip close: the route D-pad kit, Brick E, the shift laws, the one-sided left-pad extract transport, THE
STRIP, the `bottomCount = 0` corner, THE COMPLETE ROUNDTRIP, the general-path firings, the malformed negative
controls, the superseding content marker, and the terminal state.  Each must print "does not depend on any
axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.padThrough
#print axioms FX1Poly.Polygraph.unpadThrough
#print axioms FX1Poly.Polygraph.unpadThrough_padThrough
#print axioms FX1Poly.Polygraph.padThrough_injective
#print axioms FX1Poly.Polygraph.isBoundaryInvolution_padPartner
#print axioms FX1Poly.Polygraph.padThrough_isBoundaryInvolution
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_padThrough
#print axioms FX1Poly.Polygraph.isInvolutionPartner_ofIsBoundaryInvolution
#print axioms FX1Poly.Polygraph.isBoundaryInvolution_iff_validCensus
#print axioms FX1Poly.Polygraph.permInverse_zeroConsShift
#print axioms FX1Poly.Polygraph.permutationToCrossingWord_zeroConsShift
#print axioms FX1Poly.Polygraph.extractDiagram_padThrough_ofLeftPadSim
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_stripPad
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_bottomZero
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_complete
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_completeOfValidCensus
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_nestedCups
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_tripleNested
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_closedEmpty
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_loopTriple
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_cupWithLoops
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_widthEight
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_outerOverNestedLoops
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_general_monster
#print axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_stripPad_nestedCups
#print axioms FX1Poly.Polygraph.isInvolutionPartner_monster_viaConverse
#print axioms FX1Poly.Polygraph.closedMalformedCensusRejects
#print axioms FX1Poly.Polygraph.closedMalformedRoundtripFails
#print axioms FX1Poly.Polygraph.fxBrauer_hasExt5CorrectedRoundtripComplete
#print axioms FX1Poly.Polygraph.fxBrauer_closedDiagramRoundtripCloseTerminalState

end FX1PolyAudit
