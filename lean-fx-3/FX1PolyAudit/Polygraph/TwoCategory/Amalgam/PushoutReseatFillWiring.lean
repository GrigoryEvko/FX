import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutReseatFillWiring

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutReseatFillWiring — zero-axiom gate for the per-gap
decision-to-fill reseat wiring (WP-AMALG-2 r7, B1)

Per-declaration zero-axiom gate for the general reseat wiring, the two decision-driven fills, the decision-driven
end-to-end splice witness, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatGapFillOfConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatDecisionDrivenAssocFill
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatDecisionDrivenLeftUnitFill
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatDecisionDrivenSpliceWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasReseatFillWiring

end FX1PolyAudit
