import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescClassRepresentativeNormalForm

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescClassRepresentativeNormalForm — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER indexed-conv standard-form bridge: the partner-length reading
(`brauerDiagramOf_partnerLength`), the r55 roundtrip in word form (`classRepresentative_realizesDiagram`),
★ THE BRIDGE (`brauerConv_toClassRepresentative`), the normal-form laws (scope preservation + idempotence),
★ THE NORMAL FORM (`brauerConv_iff_classRepresentativeEq`), the census gates + the overrun negative control,
the general-path bridge firings (single-cup straddle landing on the r51 jam residue, multi-cup, with-cap
loop-carrying TL word), the forward-fired normal-form iff, the TEN decision pairs (kernel `decide`, both
verdicts), the content markers, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `WellFounded.fix`.
Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.brauerDiagramOf_partnerLength
#assert_no_axioms FX1Poly.Polygraph.classRepresentative_realizesDiagram
#assert_no_axioms FX1Poly.Polygraph.brauerConv_toClassRepresentative
#assert_no_axioms FX1Poly.Polygraph.classRepresentative_realizesValidInvolution
#assert_no_axioms FX1Poly.Polygraph.classRepresentative_idempotentOnValidScope
#assert_no_axioms FX1Poly.Polygraph.brauerConv_iff_classRepresentativeEq
#assert_no_axioms FX1Poly.Polygraph.censusHolds_straddleSingleCup
#assert_no_axioms FX1Poly.Polygraph.censusHolds_twoCupWord
#assert_no_axioms FX1Poly.Polygraph.censusHolds_temperleyLiebLoopWord
#assert_no_axioms FX1Poly.Polygraph.censusFails_overrunWord
#assert_no_axioms FX1Poly.Polygraph.overrunWord_representativeFailsToRealize
#assert_no_axioms FX1Poly.Polygraph.bridgeFired_straddleSingleCup
#assert_no_axioms FX1Poly.Polygraph.bridgeFired_straddleLandsOnJamResidue
#assert_no_axioms FX1Poly.Polygraph.bridgeFired_twoCupMultiCup
#assert_no_axioms FX1Poly.Polygraph.bridgeFired_temperleyLiebLoopWord
#assert_no_axioms FX1Poly.Polygraph.normalFormFired_twoCupSlide
#assert_no_axioms FX1Poly.Polygraph.decisionFired_distantCommute
#assert_no_axioms FX1Poly.Polygraph.decisionFired_nestedCirclePair
#assert_no_axioms FX1Poly.Polygraph.decisionFired_loopCountSeparates
#assert_no_axioms FX1Poly.Polygraph.decisionFired_snakeStraightens
#assert_no_axioms FX1Poly.Polygraph.decisionFired_temperleyLiebNotIdentity
#assert_no_axioms FX1Poly.Polygraph.decisionFired_temperleyLiebDeltaLoop
#assert_no_axioms FX1Poly.Polygraph.decisionFired_twoCupSlide
#assert_no_axioms FX1Poly.Polygraph.decisionFired_tripleCrossingReduces
#assert_no_axioms FX1Poly.Polygraph.decisionFired_crossingOrderSeparates
#assert_no_axioms FX1Poly.Polygraph.decisionFired_doubleDistantCancel
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasIndexedConvStandardFormBridge
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasClassRepresentativeNormalForm
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasIndexedConvRepresentativeDecisionFired
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasIndexedConvMastersAdjudication
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_classRepresentativeNormalFormTerminalState

end FX1PolyAudit
