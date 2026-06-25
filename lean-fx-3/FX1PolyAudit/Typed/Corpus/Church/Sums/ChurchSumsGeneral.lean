import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Corpus.Church.Sums.ChurchSumsGeneral

/-! # FX1PolyAudit.Typed.Corpus.Church.Sums.ChurchSumsGeneral — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.leftInjection_subst_handlerL
#assert_no_axioms FX1Poly.Typed.rightInjection_subst_handlerL
#assert_no_axioms FX1Poly.Typed.caseLeft_selectsLeftHandler_general
#assert_no_axioms FX1Poly.Typed.caseRight_selectsRightHandler_general
#assert_no_axioms FX1Poly.Typed.caseSelectsByTag_general

end FX1PolyAudit
