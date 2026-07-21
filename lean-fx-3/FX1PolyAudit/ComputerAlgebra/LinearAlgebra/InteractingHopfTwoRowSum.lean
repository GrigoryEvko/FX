import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfTwoRowSum

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfTwoRowSum —
    zero-axiom gate (the split/merge fans, the gadget tensor, and the two-row
    spatial sum)

Per-declaration zero-axiom gate for:

* the split / merge per-strand fan arities and denotations (T1: `ihtSplitLayerDomArity`,
  `ihtSplitLayerCodArity`, `ihtMergeLayerDomArity`, `ihtMergeLayerCodArity`,
  `ihtSplitLayerDenote`, `ihtMergeLayerDenote`);
* interleave injectivity (`ihtInterleaveInj`);
* the right-whisker spec and the gadget tensor (T2: `ihtWhiskerRightSpec`,
  `ihtGadgetTensorDenote`, `ihtStageACodArity`, `ihtGadgetTensorWF`,
  `ihtGadgetTensorCodArity`);
* the Minkowski / two-row-matrix membership routing (`ihtMinkowskiPairMem`);
* the five-stage assembly denotation (T3: `ihtShuffleMergeDenote`,
  `ihtShuffleMergeWF`, `ihtShuffleMergeCodArity`, `ihtGadgetShuffleMergeDenote`,
  `ihtGadgetShuffleMergeWF`, `ihtGadgetShuffleMergeCodArity`,
  `ihtUnshuffleRestDenote`, `ihtUnshuffleRestWF`, `ihtUnshuffleRestCodArity`,
  `ihtAssemblyDenote`, `ihtTwoRowSumWF`, `ihtTwoRowSumCodArity`);
* the inhabited statement (T3: `ihtTwoRowSpatialSum`) with its marker
  (`ihtHasTwoRowSpatialSum`) and kernel-decided fires
  (`ihtFireTwoRowSumFresh`, `ihtFireTwoRowSumFreshWrong`, `ihtFireTwoRowSumContent`,
  `ihtFireMinkowskiRouting`);
* the two-row NF carrier toward `ihzNormalFormStatement` (T4:
  `ihtTwoRowNormalFormCarrier`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`, `funext`, `WellFounded.fix`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ihtSplitLayerDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtSplitLayerCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtMergeLayerDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtMergeLayerCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtSplitLayerDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtMergeLayerDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtInterleaveInj
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtWhiskerRightSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtGadgetTensorDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtStageACodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtGadgetTensorWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtGadgetTensorCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtMinkowskiPairMem
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtShuffleMergeDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtShuffleMergeWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtShuffleMergeCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtGadgetShuffleMergeDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtGadgetShuffleMergeWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtGadgetShuffleMergeCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtUnshuffleRestDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtUnshuffleRestWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtUnshuffleRestCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtAssemblyDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtTwoRowSumWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtTwoRowSumCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtTwoRowSpatialSum
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtHasTwoRowSpatialSum
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtFireTwoRowSumFresh
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtFireTwoRowSumFreshWrong
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtFireTwoRowSumContent
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtFireMinkowskiRouting
#assert_no_axioms FX1Poly.ComputerAlgebra.ihtTwoRowNormalFormCarrier

end FX1PolyAudit
