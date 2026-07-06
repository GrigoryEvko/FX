import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCupPreservation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcNonCrossingCupPreservation — zero-axiom gate

Per-declaration zero-axiom gate for the CUP preservation of the non-crossing invariant (cup rung
D2a-iii, COMPLETE): the token node classification, the leg node values, the same-component
leg/old-zone dichotomy, the both-legs no-middle contradiction, the old-zone monotone position
remap, and the full `arcNonCrossing_stepCupArc` preservation.  The private clean Nat-subtraction
plumbing, the read-membership plumbing, and the node-below-implies-zone converter are covered
transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupTokenNodeClass
#assert_no_axioms FX1Poly.Polygraph.arcCupLeftLegNode
#assert_no_axioms FX1Poly.Polygraph.arcCupRightLegNode
#assert_no_axioms FX1Poly.Polygraph.arcCupSameComponentDichotomy
#assert_no_axioms FX1Poly.Polygraph.arcCupBothLegsNoMiddle
#assert_no_axioms FX1Poly.Polygraph.arcCupOldZoneMonotone
#assert_no_axioms FX1Poly.Polygraph.arcNonCrossing_stepCupArc

end FX1PolyAudit
