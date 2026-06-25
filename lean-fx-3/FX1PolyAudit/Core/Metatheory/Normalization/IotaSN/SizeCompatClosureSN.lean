import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.IotaSN.SizeCompatClosureSN

/-! # FX1PolyAudit/AuditSizeCompatClosureSN — zero-axiom gate for the generic SN-by-size combinator

Per-declaration zero-axiom gate for `FX1Poly/Core/.../IotaSN/SizeCompatClosureSN.lean`: the generic
combinator `wellFounded_of_sizeStrictlyDecreasing` (any reduction relation that strictly decreases
`RawTerm.size` is well-founded).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.wellFounded_of_natMeasureStrictlyDecreasing
#assert_no_axioms FX1Poly.Core.wellFounded_of_sizeStrictlyDecreasing

end FX1PolyAudit
