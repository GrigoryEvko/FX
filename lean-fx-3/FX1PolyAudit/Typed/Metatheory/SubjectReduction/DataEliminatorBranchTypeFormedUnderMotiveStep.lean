import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.DataEliminatorBranchTypeFormedUnderMotiveStep

/-! # FX1PolyAudit/.../DataEliminatorBranchTypeFormedUnderMotiveStep — zero-axiom gate

Per-declaration zero-axiom gate for the `piTyCode`-wrapped data-eliminator branch type-SR keystone and its
`option` / `either` instances (SR-DSL-2 type-SR content).  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.preservedUnderStep
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.preservedUnderStepStar
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.piCodeFormedUnderCodomainStep
#assert_no_axioms FX1Poly.Typed.optionMatchDependentSomeBranchType_formedUnderMotiveStep
#assert_no_axioms FX1Poly.Typed.eitherMatchDependentInlBranchType_formedUnderMotiveStep
#assert_no_axioms FX1Poly.Typed.eitherMatchDependentInrBranchType_formedUnderMotiveStep
#assert_no_axioms FX1Poly.Typed.listElimDependentConsBranchType_formedUnderMotiveStep

end FX1PolyAudit
