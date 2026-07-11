import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingStrongMonadPresentation

/-! # FX1PolyAudit.Polygraph.Omega.WalkingStrongMonadPresentationAudit — zero-axiom gate for the walking
strong monad seven-critical-pair Squier sub-presentation (WP-STRONG r1, #2189).

Per-declaration `#assert_no_axioms` on the five-label signature, the two 1-generators + three 2-generators,
the two strength legs (B1) + the sub-presentation-of-DISTLAW count partition, the five T-monad legs, the
seven critical-pair rows, the base relation, the seven generating 3-cells, the seven peak / valley joins,
the assembled resolutions and the coherent-presentation bundle, the two-strength-rows statement, the
least-congruence UP (B2), the 1-cell Parikh decision transport + both verdicts + the carrier bridge (B3),
and the commutative ledger + Moggi tie-in + negative-self-attack + census-feed / wall honesty markers (B4 / B5).
-/

namespace FX1PolyAudit

-- the five-label signature
#assert_no_axioms FX1Poly.Polygraph.Omega.StrongMonadGenLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadLabelTag
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadLabelBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadOmegaComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadOmegaModeBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadOmegaGenBeq

-- the generators
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadOmegaPoint
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadContextGen
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadEndoTGen
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadIdOne
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadCtWord
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadTcWord
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadTtWord
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadEtaGen
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMuGen
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthGen
#assert_no_axioms FX1Poly.Polygraph.Omega.allStrongMonadGenLabels
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadGeneratorLabelCountIsFive

-- B1: the two strength legs + boundary checks + non-vacuity
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthEtaLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthEtaRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthMuLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthMuRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthEtaLeftLeg_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthEtaRightLeg_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthMuLeftLeg_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthMuRightLeg_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthEtaLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthMuLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadCtTc_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadContextEndo_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthEtaLegs_notLiterallyParallelSource
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthMuLegs_notLiterallyParallelSource

-- B1: the sub-presentation-of-DISTLAW count partition
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadKeptDistLawPairs
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadDroppedDistLawPairs
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadKeptDropPartitionsDistLawFourteen
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_strengthRowsTypeCheckOnConcreteWords
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_subPresentationOfDistLawMachineChecked

-- B2: the five T-monad legs
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadUnitUnitLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadUnitUnitRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadLeftUnitAssocLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadLeftUnitAssocRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRightUnitAssocLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRightUnitAssocRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadPentagonLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadPentagonRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRootUnitAssocLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRootUnitAssocRightLeg

-- B2: the seven rows + base relation + generating 3-cells
#assert_no_axioms FX1Poly.Polygraph.Omega.StrongMonadCriticalRow
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadOmegaBaseRel
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthEtaThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthMuThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadUnitUnitThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadLeftUnitAssocThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRightUnitAssocThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadPentagonThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRootUnitAssocThreeCell

-- B2: the seven peak joins
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthEtaPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthMuPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadUnitUnitPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadLeftUnitAssocPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRightUnitAssocPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadPentagonPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRootUnitAssocPeakJoin

-- B2: the seven valley joins
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthEtaValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthMuValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadUnitUnitValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadLeftUnitAssocValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRightUnitAssocValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadPentagonValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRootUnitAssocValleyJoin

-- B2: the assembled resolutions + coherent-presentation bundle + UP
#assert_no_axioms FX1Poly.Polygraph.Omega.StrongMonadCriticalPairResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthEtaResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthMuResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadUnitUnitResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadLeftUnitAssocResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRightUnitAssocResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadPentagonResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadRootUnitAssocResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.StrongMonadWalkerCoherentPresentationStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadWalkerCoherentPresentation
#assert_no_axioms FX1Poly.Polygraph.Omega.StrongMonadTwoStrengthRowsResolvedStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadTwoStrengthRowsResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadCriticalPairsIdentifiedInEveryModel

-- B2: the census
#assert_no_axioms FX1Poly.Polygraph.Omega.StrongMonadCriticalPairLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.allStrongMonadCriticalPairs
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadCriticalPairCountIsSeven
#assert_no_axioms FX1Poly.Polygraph.Omega.allStrongMonadStrengthPairs
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadStrengthPairCountIsTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadKeptMatchesStrongCount
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadUnitUnitLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadMonadPentagonLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_sevenCriticalPairsShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_twoStrengthRowsAreBeckTwoAndFour

-- B3: the 1-cell Parikh decision transport + both verdicts + the carrier bridge
#assert_no_axioms FX1Poly.Polygraph.Omega.StrongMonadColour
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadColourToDistLaw
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadWordToDistLaw
#assert_no_axioms FX1Poly.Polygraph.Omega.StrongMonadWordConv
#assert_no_axioms FX1Poly.Polygraph.Omega.StrongMonadWordSameCount
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadConv_iffSameCount
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadWordCt
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadWordTc
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadWordCct
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadWordDecisionYes
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadWordDecisionNo
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadColourGen
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadWordToCell
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_oneCellWordProblemDecidedByParikhTransport

-- B4: the commutative ledger + Moggi tie-in + negative self-attack + census-feed markers
#assert_no_axioms FX1Poly.Polygraph.Omega.StrongMonadCommutativeAspect
#assert_no_axioms FX1Poly.Polygraph.Omega.StrongMonadCommutativeLedgerEntry
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadCommutativeLedger
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadCommutativeLedgerCountIsFour
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadCommutativeLedger_onlyStrengthShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.strongMonadCommutativeLedgerStrengthGrounded
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_commutativeMonadSeparateFollowUp
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_moggiEffectDimensionTieInNamed
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_censusFeedNewSingleObjectWalker
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_cSideBeckAxiomsUnstatable
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_strengthStrictlyWeakerThanDistLaw

-- B5: the jam ledger + r1 summary
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_fullTwoCellDecisionWalledAtTwoColourMonotoneMap
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_commutativeMonadFollowUpNotShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_fullHomotopyBasisReached
#assert_no_axioms FX1Poly.Polygraph.Omega.fxStrong_walkingStrongMonadPresentationShipped

end FX1PolyAudit
