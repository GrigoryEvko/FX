import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.ContextConversion.HasTypeUnionContextConversion

/-! # FX1PolyAudit/.../HasTypeUnionContextConversion — the zero-axiom gate for native context conversion

Per-declaration zero-axiom gate for the NATIVE single-binder context conversion (the SR-DSL-2 motive-arm
unblock): the identity-substitution condition across converted head bindings and the context-conversion master.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.identityAcrossConvertedHeadBinding_isSubstUnionTyped
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.convertHeadBinding

end FX1PolyAudit
