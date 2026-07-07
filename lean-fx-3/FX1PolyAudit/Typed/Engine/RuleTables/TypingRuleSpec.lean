import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.RuleTables.TypingRuleSpec

/-! # FX1PolyAudit.Typed.Engine.RuleTables.TypingRuleSpec — zero-axiom gate (mirror shard)

The grown-free formation typing-rule descriptor, extracted from the grown engine so the union's
formation rule-table layer reaches it without importing `HasTypeDesc`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.lmaxFold
#assert_no_axioms FX1Poly.Typed.lmaxAll
#assert_no_axioms FX1Poly.Typed.TypingRuleDesc
#assert_no_axioms FX1Poly.Typed.universeFormerOutput
#assert_no_axioms FX1Poly.Typed.nullaryFormerOutput
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_piTyCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_listCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_optionCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_unitCode
#assert_no_axioms FX1Poly.Typed.formationRuleImpliesNotVariable

end FX1PolyAudit
