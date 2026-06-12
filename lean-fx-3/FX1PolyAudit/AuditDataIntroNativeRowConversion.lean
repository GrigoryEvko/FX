import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.DataIntroNativeRowConversion

/-! # FX1PolyAudit/AuditDataIntroNativeRowConversion — zoo-to-native-rows shard

Per-declaration zero-axiom gate for the six per-family intro conversions:
every standalone intro-engine derivation rebuilds as a `HasTypeNativeUnion`
derivation through the NATIVE table-row arms alone — no `of*Intro` embedding
arm appears in any conversion, which is what makes the embedding arms
deletable.  Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeDescNatIntro.toNativeRows
#assert_no_axioms FX1Poly.Typed.HasTypeDescOptionIntro.toNativeRows
#assert_no_axioms FX1Poly.Typed.HasTypeDescEitherIntro.toNativeRows
#assert_no_axioms FX1Poly.Typed.HasTypeDescPairIntro.toNativeRows
#assert_no_axioms FX1Poly.Typed.HasTypeDescIdIntro.toNativeRows
#assert_no_axioms FX1Poly.Typed.HasTypeDescListIntro.toNativeRows

end FX1PolyAudit
