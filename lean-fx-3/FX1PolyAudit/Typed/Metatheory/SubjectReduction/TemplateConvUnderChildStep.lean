import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.TemplateConvUnderChildStep

/-! # FX1PolyAudit/.../TemplateConvUnderChildStep — the zero-axiom gate for SR-DSL-1 (generic Conv-drift)

Per-declaration zero-axiom gate for the generic Conv-drift substrate: the weakening-preserves-`Conv` helpers
(this commit) and — as they land — the `ConvChildren`-projection helpers and the mutual
`templateConvUnderChildStep`.  All must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.Conv.weakenByConv
#assert_no_axioms FX1Poly.Typed.Conv.weakenBodyUnderOneBinderByConv
#assert_no_axioms FX1Poly.Typed.Conv.weakenBodyUnderTwoBindersByConv
#assert_no_axioms FX1Poly.Typed.ConvChildren.projectShiftZero
#assert_no_axioms FX1Poly.Typed.ConvChildren.projectShiftOne
#assert_no_axioms FX1Poly.Typed.ConvChildren.projectShiftTwo
#assert_no_axioms FX1Poly.Typed.resolveProjectShiftZero
#assert_no_axioms FX1Poly.Typed.resolveProjectShiftOne
#assert_no_axioms FX1Poly.Typed.resolveProjectShiftTwo

end FX1PolyAudit
