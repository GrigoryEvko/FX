import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedUnionBindingTypeReducible
import FX1Poly.Typed.Corpus.Smoke.NativeUnionOpenStronglyNormalizing

/-! # FX1PolyAudit — native-union open strong normalization (Tier B retirement keystone)

Zero-axiom audit twin for the native-union open-SN cone: the discharged native fundamental theorem, the native
binding-type reducibility leaf, the reducible-environment builder from union well-formedness, and the two open-SN
capstones (conditional + unconditional).  Each `#assert_no_axioms` confirms no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `funext`, `native_decide`, or `omega` reached the kernel.
-/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.fundamentalAtBoundedSucc
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.subjectReducibleAsTypeUnderEnv
#assert_no_axioms FX1Poly.Typed.reducibleEnvOfWfContextUnion
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.stronglyNormalizingOfReducibleEnv
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.stronglyNormalizingOfWfContextUnion

end FX1PolyAudit
