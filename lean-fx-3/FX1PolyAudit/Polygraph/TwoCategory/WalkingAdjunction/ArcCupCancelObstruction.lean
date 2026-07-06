import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCancelObstruction

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupCancelObstruction — zero-axiom gate

Per-declaration zero-axiom gate for the cup-cancellation obstruction (peel campaign H, the
cup-cancel spike): the witness pair over the same peeled cup — chained, base-parity window,
legs fresh-separated — with EQUAL composite extracts yet DISTINCT fresh tail extracts, and
the refutation of the unconditional cup-head cancellation it yields.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupObstructionLeftTail_isChained
#assert_no_axioms FX1Poly.Polygraph.arcCupObstructionRightTail_isChained
#assert_no_axioms FX1Poly.Polygraph.arcCupObstruction_windowParityIsBase
#assert_no_axioms FX1Poly.Polygraph.arcCupObstructionLeftTail_legsSeparate
#assert_no_axioms FX1Poly.Polygraph.arcCupObstructionRightTail_legsSeparate
#assert_no_axioms FX1Poly.Polygraph.arcCupObstruction_composite_extract_eq
#assert_no_axioms FX1Poly.Polygraph.arcCupObstruction_freshTail_extract_ne
#assert_no_axioms FX1Poly.Polygraph.arcCupObstruction_diagramBlind_internalCupsSeparate
#assert_no_axioms FX1Poly.Polygraph.not_arcCupHeadCancellationUnconditional

end FX1PolyAudit
