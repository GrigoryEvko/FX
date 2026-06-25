import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnly

/-! # FX1PolyAudit/AuditHasTypeUnionNativeOnly — TYTAB-2 ADMIT foundation audit shard

Per-declaration zero-axiom gate for the ofGrown-free native union judgment + its embedding into the kernel
union judgment.  Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnionNativeOnly
#assert_no_axioms FX1Poly.Typed.HasTypeUnionNativeOnly.toUnion

end FX1PolyAudit
