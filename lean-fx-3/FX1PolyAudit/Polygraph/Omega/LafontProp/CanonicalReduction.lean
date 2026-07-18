import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.CanonicalReduction

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.CanonicalReduction — zero-axiom gate
(LAFONT-PROP r3: THE DECISION — canonicalReductionStatement REFUTED + the staged positive bricks)

Per-declaration zero-axiom gate for the r3 decision round: the derived-congruence toolkit (identity
expansions, whisker splits, interchange decompositions), the four content-mediated pad seeds, the eta
movers (extrusion chains, the scale-tower absorption, the open-index zero-stack pull and
wire-under-zeros recursion, the frontier lemma), the reduction-transfer principle, the canonical
fixed-point family, the first generator/derived instances of `canonicalReductionStatement`, the
conditional Stage-4 transfer fires, the kernel pins, AND THE REFUTATION MACHINERY: the anomaly-parity
invariant (`hasOddAnomalousBoundaryCount` with its XOR kit), the 28-constructor invariance theorem
(`convertibleDiagramsShareAnomalyParity`), the equal-matrix separator `id0 | delta`, and the three
decision theorems (`canonicalReductionStatementIsRefuted`, `matNatCompletenessStatementIsRefuted`,
`decisionCompletenessIsRefuted`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Built by the FX1PolyAudit lib glob; AuditAll registration is the next round's
bookkeeping (AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.expandIdentityAtSource
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.expandIdentityAtTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.whiskerBottomSplitsCompose
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.whiskerTopSplitsCompose
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.tensorSplitsTopThenBottom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.tensorSplitsBottomThenTop
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.padTopEtaVanishes
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.padBottomEtaVanishes
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.padTopDiscardVanishes
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.padBottomDiscardVanishes
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.etaTensorEtaAsChain
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.etaTensorEtaAsChainMirror
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addFoldsEtaPair
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.scaleWireAbsorbsEta
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zeroStackPullsEta
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.wireUnderZeroStackRecursion
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zeroGenEntersCanonicalColumn
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.reductionTransfersAlongConversion
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalFormIsItsOwnNormalForm
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalDiagramSatisfiesCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zeroSourceNormalFormIsZeroStack
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.emptyIdentitySatisfiesCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zeroGenSatisfiesCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardGenSatisfiesCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.bottomPaddedEtaSatisfiesCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.topPaddedDiscardSatisfiesCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.scaledEtaSatisfiesCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.etaPairFoldSatisfiesCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.rightNestedEtaTriple
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.etaTripleReassociates
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.rightNestedEtaTripleSatisfiesCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swappedEtaPairDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swappedEtaPairDropsSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swappedEtaPairSatisfiesCanonicalReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.unitPairReductionFollowsFromIdentityReduction
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.associativityPairReductionTransfersAcrossSides
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.rightNestedEtaTripleNormalFormIsZeroStack
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swappedEtaPairNormalFormIsZeroStack
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalSwapDiagramDecisionFires
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.scaledEtaMatricesAgreeViaSoundness
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.xorParity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.isAnomalousBoundaryPair
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.hasOddAnomalousBoundaryCount
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.xorParityFalseRight
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.xorParitySelfCancels
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.xorParityAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.xorParityInterchangeShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.convertibleDiagramsShareAnomalyParity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.leftPaddedCopyDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.leftPaddedCopyHasOddAnomaly
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.leftPaddedCopyNormalFormHasEvenAnomaly
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyGenHasEvenAnomaly
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.leftPaddedCopyDoesNotReduceToItsNormalForm
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalReductionStatementIsRefuted
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.leftPaddedCopyAgreesWithCopyOnMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.leftPaddedCopyIsNotConvertibleToBareCopy
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.matNatCompletenessStatementIsRefuted
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.decisionCompletenessIsRefuted
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.anomalyParityAgreesOnLandedConversion

end FX1PolyAudit
