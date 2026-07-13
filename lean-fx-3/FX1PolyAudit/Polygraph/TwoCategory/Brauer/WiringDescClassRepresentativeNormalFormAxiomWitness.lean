import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescClassRepresentativeNormalForm

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescClassRepresentativeNormalFormAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER indexed-conv
standard-form bridge: the partner-length reading, the word-form roundtrip, THE BRIDGE, the normal-form laws,
THE NORMAL FORM iff, the census gates, the negative controls, the general-path firings, the ten decision
pairs, the content markers, and the terminal state.  Each must print "does not depend on any axioms".
Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.brauerDiagramOf_partnerLength
#print axioms FX1Poly.Polygraph.classRepresentative_realizesDiagram
#print axioms FX1Poly.Polygraph.brauerConv_toClassRepresentative
#print axioms FX1Poly.Polygraph.classRepresentative_realizesValidInvolution
#print axioms FX1Poly.Polygraph.classRepresentative_idempotentOnValidScope
#print axioms FX1Poly.Polygraph.brauerConv_iff_classRepresentativeEq
#print axioms FX1Poly.Polygraph.censusHolds_straddleSingleCup
#print axioms FX1Poly.Polygraph.censusHolds_twoCupWord
#print axioms FX1Poly.Polygraph.censusHolds_temperleyLiebLoopWord
#print axioms FX1Poly.Polygraph.censusFails_overrunWord
#print axioms FX1Poly.Polygraph.overrunWord_representativeFailsToRealize
#print axioms FX1Poly.Polygraph.bridgeFired_straddleSingleCup
#print axioms FX1Poly.Polygraph.bridgeFired_straddleLandsOnJamResidue
#print axioms FX1Poly.Polygraph.bridgeFired_twoCupMultiCup
#print axioms FX1Poly.Polygraph.bridgeFired_temperleyLiebLoopWord
#print axioms FX1Poly.Polygraph.normalFormFired_twoCupSlide
#print axioms FX1Poly.Polygraph.decisionFired_distantCommute
#print axioms FX1Poly.Polygraph.decisionFired_nestedCirclePair
#print axioms FX1Poly.Polygraph.decisionFired_loopCountSeparates
#print axioms FX1Poly.Polygraph.decisionFired_snakeStraightens
#print axioms FX1Poly.Polygraph.decisionFired_temperleyLiebNotIdentity
#print axioms FX1Poly.Polygraph.decisionFired_temperleyLiebDeltaLoop
#print axioms FX1Poly.Polygraph.decisionFired_twoCupSlide
#print axioms FX1Poly.Polygraph.decisionFired_tripleCrossingReduces
#print axioms FX1Poly.Polygraph.decisionFired_crossingOrderSeparates
#print axioms FX1Poly.Polygraph.decisionFired_doubleDistantCancel
#print axioms FX1Poly.Polygraph.fxBrauer_hasIndexedConvStandardFormBridge
#print axioms FX1Poly.Polygraph.fxBrauer_hasClassRepresentativeNormalForm
#print axioms FX1Poly.Polygraph.fxBrauer_hasIndexedConvRepresentativeDecisionFired
#print axioms FX1Poly.Polygraph.fxBrauer_hasIndexedConvMastersAdjudication
#print axioms FX1Poly.Polygraph.fxBrauer_classRepresentativeNormalFormTerminalState

end FX1PolyAudit
