import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.Type2CompletionCyclicThreeInstance

/-! # FX1PolyAudit/Polygraph/Homology/Type2CompletionCyclicThreeInstance — zero-axiom gate (the completed
    UNSIMPLIFIED type-2 Tietze move on cyclic `⟨s | sss⟩`: the two-rule convergent presentation with its
    11-critical-pair Squier resolution, and the `H2 = 0` read-off restored by the covering critical pair)

Per-declaration zero-axiom gate for H2-SQUIER-NOGO r7 bricks B2..B4.  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B2: the completed presentation record + the confluence truth probe
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedCyclicThreePresentation
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedRewriteReduceRedexAtHead
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedNormalizeWord
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedRewriteFrontLegStep
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedRewriteBackLegStep
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedNormalFormsAreThree
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedCriticalPairOverlapWords
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedCriticalPairJoinTargets
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedCriticalPairsJoin
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedRuleTwoIsDerivable

-- B2: the boundary literals + the carrier-fit
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedBoundaryDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedBoundaryDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedBoundaryDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedPresentationBasisCounts
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedComputesBoundaryDimZero
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedComputesBoundaryDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedComputesBoundaryDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedBoundaryDimOneIsShippedType2

-- B2: the well-formedness discharge + the chain complex
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedColumnIndexBelowElevenIsAbsurd
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedPresentationIsWellFormed
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedChainComplex

-- B3: the Smith handoff + the H2 read-off (H2 = 0 restored)
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedBoundaryDimOneSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedSmithNormalFormOfDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedDimOneCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedBoundaryDimTwoSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedSmithNormalFormOfDimTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedDimTwoCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedBoundaryDimOneReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedBoundaryDimTwoReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedCyclicThreeDegreeTwoSmithData
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedDegreeTwoHomologyInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedDegreeTwoHomologyIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedBoundaryDimOneReducesToIntoLower
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedBoundaryDimTwoReducesToFromHigher
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedSmithHandoff

-- B3: the recon-prediction pin + the base agreement
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedReconPredictedH2
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedH2MatchesReconPrediction
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedH2AgreesWithCyclicBase
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedCriticalPairCountExceedsBase
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedPresentationDiffersFromBase

-- B4: the interpretation ledger (instance-level evidence, no general claim, tautological note)
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedCyclicThreeH2VindicatedAtInstance
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletionTautologicalCollapseNote
#assert_no_axioms FX1Poly.Polygraph.Homology.type2CompletedCyclicThreeLedgerResidual

end FX1PolyAudit
