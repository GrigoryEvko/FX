import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Steiner.LoopFreeOrder

/-! # FX1PolyAudit/Polygraph/Steiner/LoopFreeOrder — zero-axiom gate (the canonical SN precedence)

Per-declaration zero-axiom gate for the boundary-containment order: the dimensioned atom, the
occurs-in-boundary relation, the strict precedence, the structural-`Acc` accessibility theorem
(`Nat` induction on a dimension bound, NOT `WellFounded.fix`), and the well-foundedness export
that hands fib-3 its SN measure.  Plus the named (deferred) same-dimension order + loop-free
hypothesis.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Steiner.DimensionedAtom
#assert_no_axioms FX1Poly.Polygraph.Steiner.atomOccursInBoundaryOf
#assert_no_axioms FX1Poly.Polygraph.Steiner.precedesInBoundary
#assert_no_axioms FX1Poly.Polygraph.Steiner.boundaryContainmentAccessibleWithinDimensionBound
#assert_no_axioms FX1Poly.Polygraph.Steiner.loopFreeOrderIsWellFounded
#assert_no_axioms FX1Poly.Polygraph.Steiner.SameDimensionOrder
#assert_no_axioms FX1Poly.Polygraph.Steiner.IsLoopFreeBasis

end FX1PolyAudit
