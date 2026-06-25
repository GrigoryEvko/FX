import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.AppCongruenceSubjectReduction

/-! # FX1PolyAudit/AppCongruenceSubjectReduction — the `app` eliminator congruence SR audit shard

Per-declaration zero-axiom gate for the first arm of the native eliminator-congruence subject reduction
(gate 2 of the consistency leg, TYTAB-2-FT-SR #1697): the function-position and argument-position child
congruences for `gen_app`.  Each must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.appFunctionCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.appArgumentCongruenceSubjectReduction

end FX1PolyAudit
