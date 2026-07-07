import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable

/-! # AuditFormationRuleTable — zero-axiom gate for the TYTAB-1 formation-collapse foundation

The unified `FormationRule` descriptor + `formationRuleOf` table + the three reverse-extraction
lemmas the soundness cascade will dispatch on.  Each pin must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.FormationRule
#assert_no_axioms FX1Poly.Typed.FormationRule.outputType
#assert_no_axioms FX1Poly.Typed.formationRuleOf
#assert_no_axioms FX1Poly.Typed.formationRuleOf_boolCode
#assert_no_axioms FX1Poly.Typed.formationRuleOf_arrowCode
#assert_no_axioms FX1Poly.Typed.formationRuleOf_idCode
#assert_no_axioms FX1Poly.Typed.formationRuleOf_baseType_inv
#assert_no_axioms FX1Poly.Typed.formationRuleOf_flat_inv
#assert_no_axioms FX1Poly.Typed.formationRuleOf_termIndexed_inv

/-! ## TYTAB-2 wave U2 — the cumulative formation row wiring -/

#assert_no_axioms FX1Poly.Typed.formationRuleOf_cumulative_inv
#assert_no_axioms FX1Poly.Typed.formationRuleOf_cumulative
#assert_no_axioms FX1Poly.Typed.cumulativeFormationRuleImpliesNotVariable

/-! ## TYTAB-2 — the union-obligation form of the formation premise -/

#assert_no_axioms FX1Poly.Typed.flatFormationObligations
#assert_no_axioms FX1Poly.Typed.termIndexedEndpointObligations
#assert_no_axioms FX1Poly.Typed.FormationRule.obligations
#assert_no_axioms FX1Poly.Typed.flatFormationObligations_twoChild
#assert_no_axioms FX1Poly.Typed.FormationRule_obligations_flat_arrow
#assert_no_axioms FX1Poly.Typed.FormationRule_obligations_baseType
#assert_no_axioms FX1Poly.Typed.FormationRule_obligations_termIndexed_idCode

end FX1PolyAudit
