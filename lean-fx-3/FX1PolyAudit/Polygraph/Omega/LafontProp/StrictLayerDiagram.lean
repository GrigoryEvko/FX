import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.StrictLayerDiagram

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.StrictLayerDiagram — zero-axiom gate
(LAFONT-REPAIR stage 1, brick A+B: the unbiased strict-layer carrier)

Per-declaration zero-axiom gate for the strict-layer rebuild of the Lafont syntax: the six-cell
inventory with fixed arities (constructors asserted individually), the layer arity folds, the
cons-only cell/layer append kits with their arity algebra, wire layers, the `SldDiagram`
carrier (constructor and both projections asserted), the composability chain predicate and
computed target arity, sequential composition with `rfl`-level category laws, the zip tensor
with one-sided wire pads and THE PADDING-DISSOLUTION FIRES (`sldPaddingDissolvesOnCopy` — the
r3 separator's two sides are the SAME term), the pad-window combinator, the Mat(N) layer
semantics, the pointwise block algebra (product congruence/associativity/identity collapses,
direct-sum congruence/identity-fusion/associativity/multiplicativity, wire-layer-is-identity,
layer-append-as-blocks), the two functoriality theorems (append-as-product, zip-as-direct-sum)
with their diagram-level Bool forms, the Z2 negative-control fires, and the stage-D marker
`fxLafontStrictLayer_hasPaddingDissolution`.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Built by the FX1PolyAudit lib glob; AuditAll registration is a later
round's bookkeeping (AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldCell
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldCellSourceArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldCellTargetArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldLayer
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldLayerArityBy
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldLayerSourceArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldLayerTargetArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAppendCells
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAppendCellsNilRightIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAppendCellsAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAppendCellsArityBy
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAppendCellsSourceArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAppendCellsTargetArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldWireLayerOfArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldWireLayerArityBy
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldWireLayerSourceArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldWireLayerTargetArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldWireLayerSplitsAtCount
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldLayersAreComposableFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldLayersTargetArityFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldIsComposable
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldTargetArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAppendLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAppendLayersNilRightIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAppendLayersAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAppendLayersTargetArityFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldComposableFromAppendOfParts
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldComposableFromAppendGivesFirst
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldComposableFromAppendGivesSecond
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldIdentityDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldComposeSequential
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldComposeWithIdentitySourceIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldComposeWithIdentityTargetIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldComposeSequentialAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldComposeSequentialTargetArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldComposeSequentialIsComposable
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayersAbove
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayersBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldZipLayersWithPads
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldTensorParallel
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayersAboveWithZeroIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayersBelowWithZeroIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldTensorWithEmptyTopIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldTensorWithEmptyBottomIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldCopyDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPaddingDissolvesOnCopy
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPaddingDissolvesOnCopyBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayersAboveAreComposableFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayersAboveTargetArityFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayersBelowAreComposableFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayersBelowTargetArityFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldZipLayersAreComposableFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldZipLayersTargetArityFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldTensorParallelIsComposable
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldTensorParallelTargetArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayer
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadWindow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayerSourceArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayerTargetArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayerZeroIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadWindowZeroIsSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadWindowTargetArityFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadWindowIsComposableFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldCellEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldLayerEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldLayersDenote
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldDenote
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldIdentityDiagramDenotesIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAddLeAddLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAddLtAddLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldProductRespectsEntryAgreement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldProductAssocEntry
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldProductWithIdentityBeforeCollapses
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldProductWithIdentityAfterCollapses
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldDirectSumRespectsEntryAgreement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldDirectSumOfIdentitiesEntry
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldDirectSumAssocEntry
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldDirectSumMultiplicativityEntry
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldWireLayerEntriesAsIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAppendCellsEntriesAsBlocks
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldDenoteOfAppendAsProductEntry
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldComposeSequentialDenoteAsProduct
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayersAboveDenoteEntry
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldPadLayersBelowDenoteEntry
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldDenoteOfZipAsDirectSumEntry
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldTensorParallelDenoteAsDirectSum
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAddAfterCopyDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldZeroAfterDiscardDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldAddAfterCopyDenotesDoubling
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldZeroAfterDiscardDenotesZero
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldZSpecificPairStillSeparates
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldFireDiagramsAreWellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sldCopyDiagramDenotesCopyGen
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.fxLafontStrictLayer_hasPaddingDissolution
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldCell.wire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldCell.generatorMu
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldCell.generatorEta
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldCell.generatorDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldCell.generatorEpsilon
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldCell.crossing
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldDiagram.mk
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldDiagram.sourceArity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.SldDiagram.layers

end FX1PolyAudit
