import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingDistLawPresentation

/-! # FX1PolyAudit.Polygraph.Omega.WalkingDistLawPresentationAudit — zero-axiom gate for the walking
distributive law two-colour Squier presentation (WP-DISTLAW r1, B1).

Per-declaration `#assert_no_axioms` on the seven-label signature, the two colours plus five 2-cell
generators, the four Beck-axiom leg pairs, the colour-generic monad-leg helpers, the fourteen-row critical
relation and base relation, the four Beck generating 3-cells / peak joins / valley joins / resolutions, the
ten monad-internal generating 3-cells, the least-congruence universal property, the fourteen-row census, and
the honesty markers. -/

namespace FX1PolyAudit

-- the seven-label signature
#assert_no_axioms FX1Poly.Polygraph.Omega.DistLawGenLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawLabelTag
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawLabelBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawOmegaComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawModeBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawGenBeq

-- the two colours and five 2-cell generators
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawPoint
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawSGen
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawTGen
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawIdOne
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawStWord
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawTsWord
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawSsWord
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawTtWord
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawEtaSGen
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMuSGen
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawEtaTGen
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMuTGen
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawSwapGen

-- the four Beck-axiom leg pairs
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckOneLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckOneRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckTwoLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckTwoRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckThreeLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckThreeRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckFourLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckFourRightLeg

-- the colour-generic monad-leg helpers
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawUnitUnitLeftLegOf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawUnitUnitRightLegOf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawLeftUnitAssocLeftLegOf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawLeftUnitAssocRightLegOf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawRightUnitAssocLeftLegOf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawRightUnitAssocRightLegOf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawPentagonLeftLegOf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawPentagonRightLegOf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawRootUnitAssocLeftLegOf
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawRootUnitAssocRightLegOf

-- the fourteen-row relation and base relation
#assert_no_axioms FX1Poly.Polygraph.Omega.DistLawCriticalRow
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawOmegaBaseRel

-- the four Beck generating 3-cells
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckOneThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckTwoThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckThreeThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckFourThreeCell

-- the four Beck peak joins
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckOnePeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckTwoPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckThreePeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckFourPeakJoin

-- the four Beck valley joins
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckOneValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckTwoValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckThreeValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckFourValleyJoin

-- the assembled resolutions
#assert_no_axioms FX1Poly.Polygraph.Omega.DistLawCriticalPairResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckOneResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckTwoResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckThreeResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckFourResolved

-- the ten monad-internal generating 3-cells
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMonadSUnitUnitThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMonadSLeftUnitAssocThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMonadSRightUnitAssocThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMonadSPentagonThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMonadSRootUnitAssocThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMonadTUnitUnitThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMonadTLeftUnitAssocThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMonadTRightUnitAssocThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMonadTPentagonThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawMonadTRootUnitAssocThreeCell

-- the least-congruence universal property
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawCriticalPairsIdentifiedInEveryModel

-- the fourteen-row census
#assert_no_axioms FX1Poly.Polygraph.Omega.DistLawCriticalPairLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.allDistLawCriticalPairs
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawCriticalPairCountIsFourteen
#assert_no_axioms FX1Poly.Polygraph.Omega.allDistLawBeckPairs
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckAxiomCountIsFour
#assert_no_axioms FX1Poly.Polygraph.Omega.DistLawFourBeckAxiomsResolvedStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawFourBeckAxiomsResolved

-- the structural-distinctness and modulo-strict witnesses
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckOneLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckTwoLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckThreeLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckFourLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawStTs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckOneLegs_notLiterallyParallel
#assert_no_axioms FX1Poly.Polygraph.Omega.distLawBeckThreeLegs_notLiterallyParallel

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_fourBeckAxiomsShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_fourteenCriticalPairFamilyPresented
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_fullTwoCellDecisionWalledAtTwoColourMonotoneMap
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_fullHomotopyBasisReached

end FX1PolyAudit
