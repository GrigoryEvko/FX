import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescComponentSim

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescComponentSim — zero-axiom gate (KEYSTONE2)

Per-declaration zero-axiom gate for the generic-`WiringDesc` component substrate and the sharpened residual
reduction: the renamed-endpoint decode, the arc-fold forest preservation, the generic arc fold `componentComm`
(the same-order relabeling leg), one-step forest preservation, and the residual reduction to the block-swap
`MatchingComponentRenameRel` witness, plus the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- decoding through a renamed node list
#assert_no_axioms FX1Poly.Polygraph.wiringEndpointNode_map

-- the generic arc fold preserves the forest
#assert_no_axioms FX1Poly.Polygraph.isUnionFindForest_stepWiringArcs

-- the generic arc fold componentComm (same-order relabeling leg)
#assert_no_axioms FX1Poly.Polygraph.stepWiringArcs_componentView

-- one stepWiring step preserves the forest
#assert_no_axioms FX1Poly.Polygraph.stepWiring_links_isUnionFindForest

-- the sharpened residual reduction
#assert_no_axioms FX1Poly.Polygraph.wiringDescDisjointWindowFresh_of_componentRenameRel

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStepWiringArcsComponentView
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescResidualReduction
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescBlockSwapWitness

end FX1PolyAudit
