import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfCompilerRiffle

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfCompilerRiffle —
    zero-axiom gate for the generator-transpose riffle layer

Per-declaration zero-axiom gate for the riffle layer and the two-row spatial-sum
constructor: the crossing pair-membership spec (`ihrCrossingRowsSpec`,
`ihrCrossingLayerSpec`); the atomic swap-in-context riffle layer (`ihrSwapLayer`)
with arities and its denotation (`ihrSwapLayerDenote`); the move-past-block
cascade (`ihrMoveRight`) with the width-alignment lemmas
(`ihrMoveWidthStep`, `ihrMoveWidthRec`), cod-arity and WF; the perfect
(un)shuffle and split/merge fans (`ihrSplitLayer`, `ihrMergeLayer`,
`ihrUnshuffle`, `ihrShuffle`); the gadget tensor and the two-row-sum diagram
(`ihrGadgetTensorLayers`, `ihrTwoRowSumDiagram`); the kernel span fires; the full
concrete instances of the spatial-sum content (`ihrTwoRowSumInstanceOneOut`,
`ihrTwoRowSumInstanceTwoOut`); the owner-false residual walls
(`ihrMoveRightDenoteResidual`, `ihrUnshuffleDenoteResidual`) and the riffle-layer
marker (`ihrHasRiffleLayer`).

No new inductives/structures are introduced, so there are no constructors,
`mk`, or projections to gate — every declaration is a `def` or `theorem`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ihrCrossingRowsSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrCrossingLayerSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrSwapLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrSwapLayerDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrSwapLayerCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrSwapLayerDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrMoveRight
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrMoveWidthStep
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrMoveWidthRec
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrMoveRightCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrMoveRightWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrSplitLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrMergeLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrUnshuffle
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrShuffle
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrGadgetTensorLayers
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrTwoRowSumDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrFireSwapLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrFireMoveRight
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrFireMoveRightFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrFireUnshuffleThree
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrFireTwoRowSumOneOut
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrFireTwoRowSumFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrFireTwoRowSumThreeWide
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrTwoRowSumInstanceOneOut
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrTwoRowSumInstanceTwoOut
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrMoveRightDenoteResidual
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrUnshuffleDenoteResidual
#assert_no_axioms FX1Poly.ComputerAlgebra.ihrHasRiffleLayer

end FX1PolyAudit
