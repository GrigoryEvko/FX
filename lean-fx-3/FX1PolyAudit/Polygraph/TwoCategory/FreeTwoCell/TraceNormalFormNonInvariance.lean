import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TraceNormalFormNonInvariance

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/TraceNormalFormNonInvariance — zero-axiom gate

Per-declaration zero-axiom gate for the Eckmann–Hilton bubble falsification: the
minimal-extraction normal form is not swap-invariant, and trace equivalence is not
left-cancellable.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.bubbleGraph
#assert_no_axioms FX1Poly.Polygraph.bubbleNilPath
#assert_no_axioms FX1Poly.Polygraph.bubbleStrandPath
#assert_no_axioms FX1Poly.Polygraph.bubbleSignature
#assert_no_axioms FX1Poly.Polygraph.bubbleModeDecEq
#assert_no_axioms FX1Poly.Polygraph.bubbleModalityDecEq
#assert_no_axioms FX1Poly.Polygraph.bubbleKeyOf
#assert_no_axioms FX1Poly.Polygraph.bubbleKeyOf_injectiveOnFiber
#assert_no_axioms FX1Poly.Polygraph.bubbleKeying
#assert_no_axioms FX1Poly.Polygraph.bubbleCreationAtom
#assert_no_axioms FX1Poly.Polygraph.bubbleRightOfStrandAtom
#assert_no_axioms FX1Poly.Polygraph.bubbleAtOriginAtom
#assert_no_axioms FX1Poly.Polygraph.bubbleLeftOfStrandAtom
#assert_no_axioms FX1Poly.Polygraph.bubbleSourceTrace
#assert_no_axioms FX1Poly.Polygraph.bubbleTargetTrace
#assert_no_axioms FX1Poly.Polygraph.bubbleSourceSwapWitness
#assert_no_axioms FX1Poly.Polygraph.bubbleSwapStep
#assert_no_axioms FX1Poly.Polygraph.bubbleRepeatSwapWitness
#assert_no_axioms FX1Poly.Polygraph.bubbleRepeatSwapStep
#assert_no_axioms FX1Poly.Polygraph.bubbleSourceNormalFormComputes
#assert_no_axioms FX1Poly.Polygraph.bubbleTargetNormalFormComputes
#assert_no_axioms FX1Poly.Polygraph.bubbleNormalFormsDiffer
#assert_no_axioms FX1Poly.Polygraph.normalizeSpine_isNotSwapInvariant
#assert_no_axioms FX1Poly.Polygraph.atomicTraceEquiv_forcesSingletonEqual
#assert_no_axioms FX1Poly.Polygraph.atomicTraceEquiv_isNotLeftCancellable

end FX1PolyAudit
