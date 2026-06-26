import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.TemplateStepStarUnderChildStep

/-! # FX1PolyAudit/.../TemplateStepStarUnderChildStep — zero-axiom gate

Per-declaration zero-axiom gate for SR-DSL-2: the generic DIRECTED (`Step` ↝ `StepStar`) type-SR over the
`CellTemplate` DSL (`templateStepStarUnderChildStep` / `spineStepStarUnderChildStep`), the pointwise
`StepStarChildren` substrate (bridge + projections), the `resolveChildRef?` projection-agreement lemmas, and
the `listConsBranchType`-macro branch-type congruence.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.StepStarChildren.toChildrenStar
#assert_no_axioms FX1Poly.Typed.StepStar.ofStepStarChildren
#assert_no_axioms FX1Poly.Typed.StepStarChildren.refl
#assert_no_axioms FX1Poly.Typed.StepChildren.toStepStarChildren
#assert_no_axioms FX1Poly.Typed.StepStarChildren.projectShiftZero
#assert_no_axioms FX1Poly.Typed.StepStarChildren.projectShiftOne
#assert_no_axioms FX1Poly.Typed.StepStarChildren.projectShiftTwo
#assert_no_axioms FX1Poly.Typed.resolveProjectShiftStarZero
#assert_no_axioms FX1Poly.Typed.resolveProjectShiftStarOne
#assert_no_axioms FX1Poly.Typed.resolveProjectShiftStarTwo
#assert_no_axioms FX1Poly.Typed.listElimDependentConsBranchType_stepStable
#assert_no_axioms FX1Poly.Typed.templateStepStarUnderChildStep
#assert_no_axioms FX1Poly.Typed.spineStepStarUnderChildStep

end FX1PolyAudit
