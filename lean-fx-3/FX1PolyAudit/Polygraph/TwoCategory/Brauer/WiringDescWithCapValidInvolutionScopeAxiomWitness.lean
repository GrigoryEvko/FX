import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWithCapValidInvolutionScope

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescWithCapValidInvolutionScopeAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER r53 with-cap
valid-involution scoping: the valid-involution predicate, the exact-iff census enumerators, the cap-DUAL refutation
(the machine-checked net-loss witness `capDualRegressesAt_capCrossCup1`), the re-diagnosis witnesses (the byte-intact
r52 §D defects re-exported as malformed non-involution targets), the widened fold target, the honesty markers, and the
machine-checked terminal state.  Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.isInvolutionPartner
#print axioms FX1Poly.Polygraph.realizesValidInvolution
#print axioms FX1Poly.Polygraph.countValidInvolutionWords
#print axioms FX1Poly.Polygraph.countValidInvolutionR51Realizing
#print axioms FX1Poly.Polygraph.countRepresentativeRealizeXorValid
#print axioms FX1Poly.Polygraph.withCapValidInvolutionCount
#print axioms FX1Poly.Polygraph.withCapValidRepresentativeFailCount
#print axioms FX1Poly.Polygraph.capFreeValidCount
#print axioms FX1Poly.Polygraph.reconstructStandardFormExt5CapDual
#print axioms FX1Poly.Polygraph.classRepresentativeCapDual
#print axioms FX1Poly.Polygraph.capDualRealizes
#print axioms FX1Poly.Polygraph.countCapDualRealizing
#print axioms FX1Poly.Polygraph.countCapDualGainOverR51
#print axioms FX1Poly.Polygraph.capDualRegressesAt_capCrossCup1
#print axioms FX1Poly.Polygraph.capSideWitness0_isMalformedTarget
#print axioms FX1Poly.Polygraph.capSideWitness1_isMalformedTarget
#print axioms FX1Poly.Polygraph.capSideWitness2_isMalformedTarget
#print axioms FX1Poly.Polygraph.safeCapWord_valid_andRealizes
#print axioms FX1Poly.Polygraph.capSideWitness0_topCountInflated
#print axioms FX1Poly.Polygraph.BrauerExt5CorrectedFoldReachesValidInvolution
#print axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedExtractorValidInvolutionCoverage
#print axioms FX1Poly.Polygraph.fxBrauer_hasValidInvolutionFoldDischarged
#print axioms FX1Poly.Polygraph.fxBrauer_withCapValidInvolutionScopeTerminalState

end FX1PolyAudit
