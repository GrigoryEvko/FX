import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ClassSaturation

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ClassSaturation — zero-axiom gate

Per-declaration zero-axiom gate for the BFS class-saturation worker and both halves:
growth, seed containment, chain-reachability soundness, and fixpoint completeness
(exhausted frontier => swap-closed => the whole ~-class captured).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.listMemDecidable
#assert_no_axioms FX1Poly.Polygraph.listMemFilterInverted
#assert_no_axioms FX1Poly.Polygraph.freshSwapSuccessors
#assert_no_axioms FX1Poly.Polygraph.saturateClassWorker
#assert_no_axioms FX1Poly.Polygraph.saturateClass
#assert_no_axioms FX1Poly.Polygraph.saturateClassWorker_keepsVisited
#assert_no_axioms FX1Poly.Polygraph.saturateClass_containsSeed
#assert_no_axioms FX1Poly.Polygraph.freshSwapSuccessors_areReachable
#assert_no_axioms FX1Poly.Polygraph.saturateClassWorker_isSound
#assert_no_axioms FX1Poly.Polygraph.saturateClass_isSound
#assert_no_axioms FX1Poly.Polygraph.listMemFilterOfMem
#assert_no_axioms FX1Poly.Polygraph.IsSwapClosed
#assert_no_axioms FX1Poly.Polygraph.IsPendingOrExpanded
#assert_no_axioms FX1Poly.Polygraph.freshSwapSuccessors_coverSuccessors
#assert_no_axioms FX1Poly.Polygraph.isPendingOrExpanded_stepPreserved
#assert_no_axioms FX1Poly.Polygraph.didExhaustFrontier
#assert_no_axioms FX1Poly.Polygraph.saturateClassWorker_isSwapClosedAtFixpoint
#assert_no_axioms FX1Poly.Polygraph.saturateClass_isSwapClosed
#assert_no_axioms FX1Poly.Polygraph.isSwapClosed_containsChainTargets
#assert_no_axioms FX1Poly.Polygraph.saturateClass_isComplete
#assert_no_axioms FX1Poly.Polygraph.saturateClass_memberIffEquiv
#assert_no_axioms FX1Poly.Polygraph.decideAtomicTraceEquivViaSaturation
#assert_no_axioms FX1Poly.Polygraph.decideAtomicTraceEquiv?

end FX1PolyAudit
