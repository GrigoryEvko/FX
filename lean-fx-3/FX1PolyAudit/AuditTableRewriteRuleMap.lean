import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TableRewriteRuleMap

/-! # FX1PolyAudit/AuditTableRewriteRuleMap — IOTA-T9 rule-system shard

Per-declaration zero-axiom gate for the table-generated rewrite system:
the system definition, the table-step → rule map, the bespoke-system
inclusion (SN-130 facts become corollaries), and the strict-content
endpoint-β witness.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.fxSystemOverTable
#assert_no_axioms FX1Poly.Core.fxTableSystem
#assert_no_axioms FX1Poly.Core.StepOverTable.inducedRewriteRule
#assert_no_axioms FX1Poly.Core.StepOverTable.inducedRewriteRule_mem_fxSystemOverTable
#assert_no_axioms FX1Poly.Core.fxStepSystem_subset_fxTableSystem
#assert_no_axioms FX1Poly.Core.pathBetaRuleFixtureRedex
#assert_no_axioms FX1Poly.Core.pathBetaRuleFixtureReduct
#assert_no_axioms FX1Poly.Core.fxTableSystem_containsPathBetaRule

end FX1PolyAudit
