import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupCapStatePromotion

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyCupCapStatePromotion — zero-axiom gate
(FC-3 r34, Piece-II tail sub-node (ii): the in-valley cap seed carries every `diagramPartner_stepCupArc`
precondition, over the walking ADJOINT-TRIPLE signature)

Per-declaration zero-axiom gate for the string cap-state promotion bundle: the four preconditions
(`stringArcCapState_arcStateFresh` / `_isUnionFindForest` / `_seedBelowFresh` / `_arcBoundaryCensus`), the named
bundle `stringArcCapState_stepCupArc_preconditions`, the wide-cap chaining witness
`stringWideProbeCapBlock_chainedAtFour`, and the census truth-probe
`stringArcCapState_arcBoundaryCensus_firesOnWideValley`.  Every declaration must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the
independent `#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcCapState_arcStateFresh
#assert_no_axioms FX1Poly.Polygraph.stringArcCapState_isUnionFindForest
#assert_no_axioms FX1Poly.Polygraph.stringArcCapState_seedBelowFresh
#assert_no_axioms FX1Poly.Polygraph.stringArcCapState_arcBoundaryCensus
#assert_no_axioms FX1Poly.Polygraph.stringArcCapState_stepCupArc_preconditions
#assert_no_axioms FX1Poly.Polygraph.stringWideProbeCapBlock_chainedAtFour
#assert_no_axioms FX1Poly.Polygraph.stringArcCapState_arcBoundaryCensus_firesOnWideValley
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCupCapStatePromotion

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringArcCapState_arcStateFresh
#print axioms FX1Poly.Polygraph.stringArcCapState_isUnionFindForest
#print axioms FX1Poly.Polygraph.stringArcCapState_seedBelowFresh
#print axioms FX1Poly.Polygraph.stringArcCapState_arcBoundaryCensus
#print axioms FX1Poly.Polygraph.stringArcCapState_stepCupArc_preconditions
#print axioms FX1Poly.Polygraph.stringWideProbeCapBlock_chainedAtFour
#print axioms FX1Poly.Polygraph.stringArcCapState_arcBoundaryCensus_firesOnWideValley
#print axioms FX1Poly.Polygraph.fxString_hasCupCapStatePromotion

end FX1PolyAudit
