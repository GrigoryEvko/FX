import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.StrongSteiner

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/StrongSteiner — zero-axiom gate (OMEGA-2 B1 admission)

Per-declaration `#assert_no_axioms` on the `isStrongSteiner` interface line: the bounded Bool
quantifiers, the overlap edge / reachability / cycle detection, the loop-free and direct-atomic
conjuncts, the admission predicate, and the two-object support-cycle cross-check complex.  Every
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.anyIndexBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.allIndexBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.isNonzeroInt
#assert_no_axioms FX1Poly.Polygraph.Omega.overlapEdgeBool
#assert_no_axioms FX1Poly.Polygraph.Omega.overlapReachableWithin
#assert_no_axioms FX1Poly.Polygraph.Omega.hasOverlapCycleAtFaceDim
#assert_no_axioms FX1Poly.Polygraph.Omega.isStronglyLoopFreeUpTo
#assert_no_axioms FX1Poly.Polygraph.Omega.entryIsSignPure
#assert_no_axioms FX1Poly.Polygraph.Omega.entryIsSignPure_true
#assert_no_axioms FX1Poly.Polygraph.Omega.decideAtomicDirect
#assert_no_axioms FX1Poly.Polygraph.Omega.isStrongSteiner
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicBasisCount
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicBoundaryMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicComplex

end FX1PolyAudit
