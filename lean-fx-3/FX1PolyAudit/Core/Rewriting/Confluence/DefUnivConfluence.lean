import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Confluence.DefUnivConfluence

/-! # AuditDefUnivConfluence — zero-axiom gate for DEFUNIV-CONFLUENCE (#1422)

The univalence-shaped definitional-univalence row joins the canonical
βι table orthogonally (IOTA-T5) and confluently (IOTA-T6).  Each shipped
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.candidateUnivalenceTable_isWf
#assert_no_axioms FX1Poly.Core.univalenceShapedDemoRule_isScopeUniform
#assert_no_axioms FX1Poly.Core.appendedUnivalenceRowKeepsScopeUniform
#assert_no_axioms FX1Poly.Core.candidateUnivalenceTable_isScopeUniform
#assert_no_axioms FX1Poly.Core.candidateUnivalenceTable_isConfluent

end FX1PolyAudit
