import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfRowGadget

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfRowGadget — zero-axiom
    gate (WP-PROP-3 brick 6: the single-row IH_Q gadget)

Per-declaration zero-axiom gate for the `R = 1` matrix -> diagram reifier: the
scalar-layer constructors (`ihgScalarLayer`, `ihgScalarMirrorLayer`) with their
arities/all-width lemmas and the per-strand denotation theorems
(`ihgScalarLayerDenote`, `ihgScalarMirrorLayerDenote`); the pointwise-scale
bridge (`ihgPointwiseScale`, `ihgPointwiseScaleReplicate`); the two half-gadgets
(`ihgCollapseDiagram`, `ihgExpandDiagram`) with arities/WF/all-width and the
line-span denotation theorems (`ihgCollapseDenote`, `ihgExpandDenote`); the
four-stage single-row gadget (`ihgGadgetDiagram`) with arities/WF and the
line-span denotation theorem (`ihgGadgetDenote`); the single-row NF carrier
instance (`ihgSingleRowNormalForm`); the kernel span fires; the two `true`
markers plus the owner-false multi-row wall (`ihgTwoRowSpatialSumStatement`,
`ihgHasMultiRowRiffle`).

No new inductives/structures are introduced, so there are no constructors,
`mk`, or projections to gate — every declaration is a `def` or `theorem`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ihgScalarLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgScalarMirrorLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgScalarLayerDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgScalarLayerCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgScalarMirrorLayerDomArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgScalarMirrorLayerCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgScalarLayerAllWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgScalarMirrorLayerAllWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgPointwiseScale
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgScalarLayerDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgScalarMirrorLayerDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgHasScalarLayerTensor
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgPointwiseScaleReplicate
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgCollapseDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgExpandDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgCollapseCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgCollapseWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgCollapseCodArityDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgExpandCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgExpandWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgExpandCodArityDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgCollapseAllWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgExpandAllWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgCollapseDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgExpandDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgGadgetDiagram
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgGadgetCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgGadgetWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgGadgetDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgHasSingleRowGadget
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgSingleRowNormalForm
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgFireScalarLayerTwoHalf
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgFireGadgetOneOne
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgFireGadgetTwoOne
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgFireGadgetOneTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgFireGadgetOneOneWrong
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgTwoRowSpatialSumStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.ihgHasMultiRowRiffle

end FX1PolyAudit
