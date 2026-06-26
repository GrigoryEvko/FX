import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.FormationObligationSize

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.FormationObligationSize — zero-axiom gate

Per-declaration zero-axiom gate for the formation obligation-subject size bounds across ALL families
(SR-WF-TIEOFF step 2): the recursive term-indexed-endpoint bound, the finite-dispatch cumulative bound, and the
table-driven combiner over `FormationRule`. Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.termIndexedEndpointObligationSubjectSizeBound
#assert_no_axioms FX1Poly.Typed.cumulativeFormationObligationSubjectSizeBound
#assert_no_axioms FX1Poly.Typed.formationRuleObligationSubjectSizeBound

end FX1PolyAudit
