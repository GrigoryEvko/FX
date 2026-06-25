import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Core.StepRewriteRuleMap

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Core.StepRewriteRuleMap

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Core.StepRewriteRuleMap`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Each FX reduction as a rewrite rule over the term-code word monoid.  Uses the faithful RawTerm.toCode
-- (head tag + payload + children) as the bridge encode.  toCode_mkGen (rfl head-tag rule) + toCode_ne_nil
-- (every code begins with the head tag, so non-degenerate rules).  Step.inducedRewriteRule maps a reduction to
-- the rule (redex.toCode, reduct.toCode); projections rfl + both-sides-non-empty.  fxStepSystem is the
-- generated rule system (a rule is in it iff it is some reduction's code-pair); inducedRewriteRule_mem proves
-- every Step lands in it by construction.  Zero-axiom: rfl / cases + cons_ne_nil / existential-intro with rfl
-- witnesses.
#assert_no_axioms FX1Poly.Core.toCode_mkGen

#assert_no_axioms FX1Poly.Core.toCode_ne_nil

#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule

#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_leftHandSide

#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_rightHandSide

#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_leftHandSide_ne_nil

#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_rightHandSide_ne_nil

#assert_no_axioms FX1Poly.Core.fxStepSystem

#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_mem_fxStepSystem

end FX1PolyAudit
