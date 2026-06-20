import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable

/-! # AuditFormationRuleTable — zero-axiom gate for the TYTAB-1 formation-collapse foundation

The unified `FormationRule` descriptor + `formationRuleOf` table + the three reverse-extraction
lemmas the soundness cascade will dispatch on.  Each pin must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.FormationRule
#assert_no_axioms FX1Poly.Typed.FormationRule.premiseHolds
#assert_no_axioms FX1Poly.Typed.FormationRule.outputType
#assert_no_axioms FX1Poly.Typed.formationRuleOf
#assert_no_axioms FX1Poly.Typed.formationRuleOf_boolCode
#assert_no_axioms FX1Poly.Typed.formationRuleOf_arrowCode
#assert_no_axioms FX1Poly.Typed.formationRuleOf_idCode
#assert_no_axioms FX1Poly.Typed.formationRuleOf_baseType_inv
#assert_no_axioms FX1Poly.Typed.formationRuleOf_flat_inv
#assert_no_axioms FX1Poly.Typed.formationRuleOf_termIndexed_inv

end FX1PolyAudit
