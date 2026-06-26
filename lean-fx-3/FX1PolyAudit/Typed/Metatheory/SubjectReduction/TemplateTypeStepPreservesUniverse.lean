import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.TemplateTypeStepPreservesUniverse

/-! # FX1PolyAudit/.../TemplateTypeStepPreservesUniverse — zero-axiom gate

Per-declaration zero-axiom gate for the SR-DSL-2 capstone `templateTypeStepPreservesUniverse` (the generic
type-SR over the `CellTemplate` DSL = directed congruence ∘ universe rigidity).  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.templateTypeStepPreservesUniverse

end FX1PolyAudit
