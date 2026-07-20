import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfNormalFormCompiler

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfNormalFormCompiler —
    zero-axiom gate (WP-PROP-3 brick 11: the general NF compiler and the IH_Q
    word-problem decision)

Per-declaration zero-axiom gate for:

* the gadget-sub-diagram tensor (T1: `ihxGadgetSubLayers`, `ihxStageACodArity`,
  `ihxGadgetSubTensorCodArity`, `ihxGadgetSubTensorWF`, `ihxGadgetSubTensorDenote`,
  `ihxHasGadgetSubTensor`);
* the general assembly (T2: `ihxGadgetSubShuffleMergeWF`,
  `ihxGadgetSubShuffleMergeCodArity`, `ihxGadgetSubShuffleMergeDenote`,
  `ihxUnshuffleGadgetSubWF`, `ihxUnshuffleGadgetSubCodArity`,
  `ihxUnshuffleGadgetSubDenote`, `ihxGeneralAssemblyDenote`,
  `ihxHasGeneralAssembly`);
* the row-list recursion and the NF compiler (T3: `ihxRowConsDiagram`,
  `ihxRowConsDiagramWF`, `ihxRowConsDiagramCodArity`, `ihxConsPairMem`,
  `ihxNormalFormCarrier`, `ihxNormalFormCompiler`, `ihxHasNormalFormCompiler`);
* the IH_Q word-problem decision (T4: `ihxSpanDecision`, `ihxDiagramWordProblem`,
  `ihxNormalFormWordProblem`, `ihxHasWordProblemDecision`);
* the committed statement inhabited VERBATIM (`ihxNormalFormStatementVerbatim`) and
  the kernel-decided fires (`ihxFireNFCompilerRunsThreeRow`, `ihxFireNFTwoRowDiagram`,
  `ihxFireNFTwoRowSpan`, `ihxFireNFTwoRowSpanWrong`, `ihxFireDecisionEqual`,
  `ihxFireDecisionUnequal`, `ihxFireDecisionContent`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`, `funext`, `WellFounded.fix`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ihxGadgetSubLayers
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxStageACodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxGadgetSubTensorCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxGadgetSubTensorWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxGadgetSubTensorDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxHasGadgetSubTensor
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxGadgetSubShuffleMergeWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxGadgetSubShuffleMergeCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxGadgetSubShuffleMergeDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxUnshuffleGadgetSubWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxUnshuffleGadgetSubCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxUnshuffleGadgetSubDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxGeneralAssemblyDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxHasGeneralAssembly
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxRowConsDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxRowConsDiagramWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxRowConsDiagramCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxConsPairMem
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxNormalFormCarrier
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxNormalFormCompiler
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxHasNormalFormCompiler
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxSpanDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxDiagramWordProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxNormalFormWordProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxHasWordProblemDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxNormalFormStatementVerbatim
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxFireNFCompilerRunsThreeRow
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxFireNFTwoRowDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxFireNFTwoRowSpan
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxFireNFTwoRowSpanWrong
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxFireDecisionEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxFireDecisionUnequal
#assert_no_axioms FX1Poly.ComputerAlgebra.ihxFireDecisionContent

end FX1PolyAudit
