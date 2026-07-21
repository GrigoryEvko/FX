import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfCompiler

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfCompiler — zero-axiom
    gate for the matrix -> diagram fan kit

Per-declaration zero-axiom gate for the copy/add/mult fan kit: the diagonal and
sum targets (`ihcReplicate`, `ihcSum`), the copy fan cascade with arities/WF, the
add fan cascade with arities/WF, the mult (cocopy) fan cascade with arities/WF,
the kernel span fires, the grow/shrink layer characterizations
(`ihcCopyGrowRel`, `ihcAddShrinkRel`, `ihcMultShrinkRel`), the replicate/sum
bookkeeping (`ihcReplicateSnoc`, `ihcReplicateSnocTwo`, `ihcSumCat`,
`ihcAddFanUncons`), the three arbitrary-width denotation theorems
(`ihcCopyFanDenote`, `ihcAddFanDenote`, `ihcMultFanDenote`), and the T1
fan-kit marker.

No new inductives/structures are introduced, so there are no constructors,
`mk`, or projections to gate — every declaration is a `def` or `theorem`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ihcReplicate
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcReplicateLength
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcSum
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyFanLayers
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyFanDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyGrowLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyGrowLayerDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyGrowLayerCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyFanCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyFanWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyFanDiagramCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyFanDiagramWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddFanLayers
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddFanDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddShrinkLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddShrinkLayerDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddShrinkLayerCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddFanCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddFanWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddFanDiagramCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddFanDiagramWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcFireCopyFanDiscard
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcFireCopyFanWire
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcFireCopyFanTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcFireCopyFanThree
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcFireAddFanWire
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcFireAddFanTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcReplicateSnoc
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcReplicateSnocTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyGrowRel
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyGrowReplicate
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcCopyFanDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcSumCat
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddShrinkRel
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddFanUncons
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcAddFanDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcMultFanLayers
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcMultFanDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcMultShrinkLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcMultShrinkLayerDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcMultShrinkLayerCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcMultFanCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcMultFanWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcMultFanDiagramCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcMultFanDiagramWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcMultShrinkRel
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcMultFanDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcFireMultFanUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcFireMultFanTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.ihcHasFanKit

end FX1PolyAudit
