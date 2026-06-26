import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.FlatFormationObligationSize

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.FlatFormationObligationSize — zero-axiom gate

Per-declaration zero-axiom gate for the flat-formation obligation-subject size bound (SR-WF-TIEOFF step 2, flat
family). Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.flatFormationObligationSubjectSizeBound

end FX1PolyAudit
