import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionInvariantModel

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCohesion.CohesionInvariantModel — zero-axiom gate (boundedness REFUTED)

Per-declaration zero-axiom gate for the r3 invariant-model lane: the clean `Nat` rearrangement primitives
(hand-proven right cancellation + middle-four), the generic `Nat` count homomorphism and its structural soundness
over `TwoCellStep` / `TwoCellConv` / `TwoCellConvFull` / `castBoundary`, the cohesion two-count weights and the
flat-degree balance (the `ℤ` invariant realized `propext`-free), its saturated-congruence soundness, the flat
bubble + the unit-hom pump family, the infinitude witnesses (injection `ℕ ↪` classes, non-convertibility of
distinct levels, no finite representative set), the non-vacuity verdicts (r2 pair `isFalse`, idempotence + triangle
`isTrue`), and the honesty markers.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natMiddleFour
#assert_no_axioms FX1Poly.Polygraph.genCount
#assert_no_axioms FX1Poly.Polygraph.genCount_castBoundary
#assert_no_axioms FX1Poly.Polygraph.genCount_step
#assert_no_axioms FX1Poly.Polygraph.genCount_conv
#assert_no_axioms FX1Poly.Polygraph.genCount_convFull
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatUpWeight
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatDownWeight
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatUpCount
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatDownCount
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatUpCount_convFull
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatDownCount_convFull
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatBalanced
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatBalance_trans
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatBalance_addBoth
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatBalance_addBothLeft
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatBalanced_satConv
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatBubbleCell
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatBubble_upCount
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatBubble_downCount
#assert_no_axioms FX1Poly.Polygraph.cohesionUnitPumpCell
#assert_no_axioms FX1Poly.Polygraph.cohesionUnitPumpCell_upCount
#assert_no_axioms FX1Poly.Polygraph.cohesionUnitPumpCell_downCount
#assert_no_axioms FX1Poly.Polygraph.cohesionUnitHom_hasCellOfEveryFlatDegree
#assert_no_axioms FX1Poly.Polygraph.cohesionUnitPump_injectiveModConv
#assert_no_axioms FX1Poly.Polygraph.cohesionUnitPump_notConvertible_of_ne
#assert_no_axioms FX1Poly.Polygraph.cohesionUnitHom_notPerBoundaryBounded
#assert_no_axioms FX1Poly.Polygraph.cohesionR2Pair_flatCounts
#assert_no_axioms FX1Poly.Polygraph.cohesionR2Pair_notConvertible
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatBalance_decidesThreeNonVacuously
#assert_no_axioms FX1Poly.Polygraph.decideCohesionR2Pair
#assert_no_axioms FX1Poly.Polygraph.decideCohesionIdempotencePair
#assert_no_axioms FX1Poly.Polygraph.decideCohesionTrianglePair
#assert_no_axioms FX1Poly.Polygraph.fxCohesion_hasFlatDegreeInvariant
#assert_no_axioms FX1Poly.Polygraph.fxCohesion_hasPerBoundaryBoundedness
#assert_no_axioms FX1Poly.Polygraph.fxCohesion_hasUnitHomDecision

end FX1PolyAudit
