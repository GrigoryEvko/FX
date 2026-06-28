import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.StepPreservesDimensionalSubjectUsability

/-! # FX1PolyAudit/StepPreservesDimensionalSubjectUsability — dimensional usability bridge audit shard

Per-declaration zero-axiom gate for the `.dimensional` usability bridge (the dual of the `.fibrant`
`stepPreservesFibrantSubjectUsability`): the typed-at-interval ⟹ dimensionally-usable bridge under the
interval-non-fibrancy discipline `NoConsBindingIsInterval`, and the SR-residual closer that discharges the
`pathApp`-argument congruence's dimensional residual.  Each must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.typedAtIntervalImpliesDimensionallyUsable_ofNoConsInterval
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.stepPreservesDimensionalSubjectUsability

end FX1PolyAudit
