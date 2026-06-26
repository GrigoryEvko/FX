import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.FormationBoundedChildSubjectReduction

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.FormationBoundedChildSubjectReduction — zero-axiom gate

Per-declaration zero-axiom gate for the bridge that runs the formation congruence gate on the fuel-bounded
child-SR (SR-WF-TIEOFF step 3, formation family). Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.formationGateInlineChildSubjectReductionOfBelow

end FX1PolyAudit
