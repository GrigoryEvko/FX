import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpinePathChain

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SpinePathChain — zero-axiom gate

Per-declaration zero-axiom gate for the path-level chain discipline: the boundary-path
accessors, the chain inductive with its cons inversion, the four-factor reassociation, the
two swap-preservation directions, and the class-invariant transfer along the atomic trace
equivalence.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SpineAtom.domBoundaryPath
#assert_no_axioms FX1Poly.Polygraph.SpineAtom.codBoundaryPath
#assert_no_axioms FX1Poly.Polygraph.SpinePathChained
#assert_no_axioms FX1Poly.Polygraph.spinePathChained_tail
#assert_no_axioms FX1Poly.Polygraph.composePath_middleAssoc
#assert_no_axioms FX1Poly.Polygraph.SpineAtomSwap.preservesPathChain
#assert_no_axioms FX1Poly.Polygraph.SpineAtomSwap.reflectsPathChain
#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.pathChainedTransfer

end FX1PolyAudit
