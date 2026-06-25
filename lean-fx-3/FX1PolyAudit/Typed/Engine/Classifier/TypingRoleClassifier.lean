import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.TypingRoleClassifier

/-! # FX1PolyAudit.Typed.Engine.Classifier.TypingRoleClassifier — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_excludesIntro
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_excludesElim
#assert_no_axioms FX1Poly.Typed.introRuleDescOf_excludesElim
#assert_no_axioms FX1Poly.Typed.elimRuleDescOf_excludesIntro
#assert_no_axioms FX1Poly.Typed.TypingRole
#assert_no_axioms FX1Poly.Typed.typingRoleOf
#assert_no_axioms FX1Poly.Typed.typingRoleOf_formation_of
#assert_no_axioms FX1Poly.Typed.typingRoleOf_intro_of
#assert_no_axioms FX1Poly.Typed.typingRoleOf_elim_of
#assert_no_axioms FX1Poly.Typed.typingRoleOf_isNone_iff
#assert_no_axioms FX1Poly.Typed.typingRoleOf_piTyCode_smoke
#assert_no_axioms FX1Poly.Typed.typingRoleOf_lam_smoke
#assert_no_axioms FX1Poly.Typed.typingRoleOf_app_smoke
#assert_no_axioms FX1Poly.Typed.typingRoleOf_boolTrue_smoke

end FX1PolyAudit
