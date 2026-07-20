import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfWhisker

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfWhisker — zero-axiom
    gate (WP-PROP-3 brick 3: the IH_Q whisker congruence)

Per-declaration zero-axiom gate for the IH_Q whisker congruence: the row-list
plumbing (cat nil/assoc, span/pair-membership casts, the id-rows pins), the
tensor embed linearity kit (length/zero/add/scale both factors + the
block-recombination lemma), THE TENSOR SPEC (`ihwTensorSpec`), the tensor laws
(cong, id-sum, units, assoc, THE INTERCHANGE), the cell/wire/layer-list
concatenation plumbing with the layer split and sequential decomposition, the
whisker stack (layer/layers whiskering with arities, WF, zero-collapse, and
the denotation theorems), the pad combinator (WF/cod-arity/denote-decomp/
identity), the window moves (`IhwWindowMove` incl. the layer-split exchange
with its bundle), the padded step (`IhwStep` + `ihwStepBundle`), the whisker
congruence `IhwConv` with soundness (`ihwConvSound`), the refutation bridge
(`ihwConvSpanEqB`), the row fire through the identity pad, the context
closures and THE EMBEDDING of the committed sequential congruence
(`ihwConvOfSeedConv`), the T4/T5 fires (four committed rows re-fired inside
parallel contexts with kernel span pins, the two-redex parallel derivation,
the layer-split fire, the carried-over FALSE controls), and the supersession
markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ihwCatNilRight
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwCatAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwMemSpanCast
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwPairMemCast
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwIdRowsZeroIsNil
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWireCellRowsAreIdOne
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorEmbedFirstLength
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorEmbedFirstZero
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorEmbedFirstAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorEmbedFirstScale
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorEmbedSecondLength
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorEmbedSecondZero
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorEmbedSecondAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorEmbedSecondScale
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorEmbedAddBlocks
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorRowsCong
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorIdSum
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorUnitLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorUnitRight
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorRowsAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwTensorComposeInterchange
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwCatCells
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwCatCellsNilRight
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwCatCellsDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwCatCellsCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWireCells
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWireCellsDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWireCellsCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWireCellsDenoteId
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwLayerDenoteCatSplit
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwCatLayers
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwCatLayersNilRight
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwLayersCodArityCat
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwLayersWFCat
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwLayersDenoteCat
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwSnocCatLayers
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWhiskerLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWhiskerLayers
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWhiskerLayerDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWhiskerLayerCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWhiskerLayersCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWhiskerLayersWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWhiskerLayersZero
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWhiskerLayerDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWhiskerLayersDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwPadDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwPadDiagramWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwPadDiagramCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwPadDiagramDenoteDecomp
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwPadDiagramIdentityAt
#assert_no_axioms FX1Poly.ComputerAlgebra.IhwWindowMove
#assert_no_axioms FX1Poly.ComputerAlgebra.IhwWindowMove.row
#assert_no_axioms FX1Poly.ComputerAlgebra.IhwWindowMove.splitLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwSplitLayerBundle
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwWindowMoveBundle
#assert_no_axioms FX1Poly.ComputerAlgebra.IhwStep
#assert_no_axioms FX1Poly.ComputerAlgebra.IhwStep.pad
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwStepBundle
#assert_no_axioms FX1Poly.ComputerAlgebra.IhwConv
#assert_no_axioms FX1Poly.ComputerAlgebra.IhwConv.step
#assert_no_axioms FX1Poly.ComputerAlgebra.IhwConv.refl
#assert_no_axioms FX1Poly.ComputerAlgebra.IhwConv.symm
#assert_no_axioms FX1Poly.ComputerAlgebra.IhwConv.trans
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwConvSound
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwConvSpanEqB
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwRowConv
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwConvPrependLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwConvAppendLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwConvOfSeedConv
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireCounitRowInParallelContext
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireCounitRowInParallelContextSpanPin
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireScalarProductRowBesideWire
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireScalarProductRowBesideWireSpanPin
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireWhiteSpecialRowUnderTwoWires
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireWhiteSpecialRowUnderTwoWiresSpanPin
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireAddUnitRowBetweenWires
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireAddUnitRowBetweenWiresSpanPin
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireTwoScalarRedexesInParallel
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireTwoScalarRedexesInParallelSpanPin
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireSplitScalarPairLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireSplitScalarPairLayerSpanPin
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireUnitsNotConv
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwFireScalarTwoThreeNotConv
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwHasTensorSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwHasInterchange
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwHasWhiskerCongruence
#assert_no_axioms FX1Poly.ComputerAlgebra.ihwHasSeedEmbedding

end FX1PolyAudit
