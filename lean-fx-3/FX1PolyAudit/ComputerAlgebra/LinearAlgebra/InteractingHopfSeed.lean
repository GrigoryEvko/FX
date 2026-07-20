import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfSeed

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfSeed — zero-axiom
    gate (WP-PROP-3 brick 2: the IH_Q presentation seed)

Per-declaration zero-axiom gate for the IH_Q presentation seed: the executable
helper kit (Nat equality, Bool conjunction, casts), the IH_Q cell syntax over
the BSZ self-dual signature with per-cell generator matrices and the mirror
converse pins, the minimal layer tensor (interleaved direct sum, definition +
width), strict layers / the diagram carrier with the executable
well-formedness gate, relation equivalence with both span bridges, the QnfRat
identity spec (`ihsIdSpec`) with its padded-pair transform lemmas, the
categorical laws (compose cong/assoc/unit), the snoc plumbing with the
sequential decomposition (`ihsLayersDenoteSnoc`), THE RELATION SET — all 46
IH_Q rows (`IhsRowTag` + lhs/rhs) with THE GATE (`ihsRowGateFires` /
`ihsRowSpanGate`) and the two general-scalar absorb theorems, the
convertibility bundle + the sequential congruence `IhsConv` with soundness
(`ihsConvSound`) and the refutation bridge (`ihsConvSpanEqB`), the fires
(TRUE conv in context, FALSE controls with `Not IhsConv`, the scalar
composition), and the honesty markers incl. the owner-false whisker wall and
completeness statement.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ihsNatEqB
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsNatEqBSound
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsAndB
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsAndBTrueLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsAndBTrueRight
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLengthZeroNil
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsAllWidthCast
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.whiteMult
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.whiteUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.blackComult
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.blackCounit
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.whiteComult
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.whiteCounit
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.blackMult
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.blackUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.scalarBox
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.scalarBoxMirror
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.wire
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsCell.crossing
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsCellDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsCellCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsCellRows
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsCellRowsWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsScalarTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsScalarThree
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsScalarFive
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsScalarSix
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsAntipodeScalar
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsMirrorCoaddIsConverseOfAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsMirrorCocopyIsConverseOfCopy
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsMirrorBlackUnitIsConverseOfDiscard
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsMirrorCozeroIsConverseOfZero
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsMirrorScalarTwoIsConverse
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsTensorEmbedFirst
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsTensorEmbedSecond
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsTensorRows
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsTensorRowsWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayerDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayerCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayerDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayerDenoteWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayersCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsLayersWF
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsLayersWF.nil
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsLayersWF.cons
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayersWFCast
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayersDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayersDenoteWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsDiagram.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsDiagram.sourceArity
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsDiagram.layers
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsDiagramCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsDiagramWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsDiagramDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsDiagramDenoteWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayersWFB
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayersWFOfB
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsDiagramWFB
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsDiagramWFOfB
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRelEquiv
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRelEquivRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRelEquivSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRelEquivTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRelEquivCast
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRelEquivOfSpanIff
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsSpanIffOfRelEquiv
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRelEquivOfSpanEqB
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsSpanEqBOfRelEquiv
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsPadPairRowZero
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsPadPairRowAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsPadPairRowScale
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsIdHeadCombine
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsIdSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsComposeRowsCong
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsComposeRowsAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsComposeIdLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsComposeIdRight
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsSnocLayers
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayersCodAritySnoc
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayersWFSnoc
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsLayersDenoteSnoc
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.addUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.addComm
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.addAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.copyCounit
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.copyCocomm
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.copyCoassoc
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.addDiscard
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.bimonoid
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.zeroCopy
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.zeroDiscard
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarOne
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarProduct
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarThroughAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarAfterZero
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarThroughCopy
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarIntoDiscard
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarZeroBox
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarSum
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.coaddCounit
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.coaddCocomm
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.coaddCoassoc
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.cocopyUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.cocopyComm
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.cocopyAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.unitCoadd
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.bimonoidOp
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.cocopyCozero
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.unitCozero
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarOneOp
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarProductOp
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarThroughCoaddOp
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarIntoCozeroOp
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarThroughCocopyOp
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarAfterUnitOp
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarZeroBoxOp
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.scalarSumOp
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.forwardCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.backwardCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.whiteFrobeniusLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.whiteFrobeniusRight
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.blackFrobeniusLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.blackFrobeniusRight
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.whiteBlackCup
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.whiteBlackCap
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.whiteSpecial
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsRowTag.blackSpecial
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRowLhs
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRowRhs
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRowGateB
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRowGateFires
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRowSpanGate
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsScalarZeroAbsorbGeneral
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsScalarCozeroAbsorbGeneral
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsConvBundle
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsConvBundleSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsConvBundleTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsConvBundleOfChecks
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsRowBundle
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsConv
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsConv.row
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsConv.reflWF
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsConv.symm
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsConv.trans
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsConv.prependLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.IhsConv.appendLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsConvSound
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsConvSpanEqB
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsFireCounitRowInScalarContext
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsFireScalarOneRowThenAppendedScalar
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsWhiteUnitDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsBlackUnitDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsFireUnitsSpanDistinct
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsFireUnitsNotConv
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsScalarTwoDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsScalarThreeDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsFireScalarTwoThreeSpanDistinct
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsFireScalarTwoThreeNotConv
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsFireScalarCompositionSpan
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsFireScalarCompositionConv
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsFireIllFormedDetected
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsHasDiagramSemantics
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsHasRowGate
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsHasSoundness
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsHasWhiskerCongruence
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsCompletenessStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.ihsCompletenessIsProven

end FX1PolyAudit
