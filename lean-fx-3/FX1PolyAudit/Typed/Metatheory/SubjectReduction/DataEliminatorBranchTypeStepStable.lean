import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.DataEliminatorBranchTypeStepStable

/-! # FX1PolyAudit/.../DataEliminatorBranchTypeStepStable — zero-axiom gate

Per-declaration zero-axiom gate for the option / either dependent branch-type `stepStable` family (the directed
classifier-drift the context-fixed driver consumes for these eliminators).  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.optionMatchDependentSomeBranchType_stepStable
#assert_no_axioms FX1Poly.Typed.eitherMatchDependentInlBranchType_stepStable
#assert_no_axioms FX1Poly.Typed.eitherMatchDependentInrBranchType_stepStable
#assert_no_axioms FX1Poly.Typed.idJMotiveAt_bodyStepStable

end FX1PolyAudit
