import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.GeneratorSignatureValue

/-! # FX1PolyAudit/AuditGeneratorSignatureValue — SIG-1 signature-value audit shard

Per-declaration zero-axiom gate for the SIG-1 spike: the `Generator.descriptor`
materialiser, the `GeneratorDescriptor.toGenerator` inverse, the two
signature-VALUE forms (`fxSignatureLookup` function + `fxSignature` list),
the round-trip ≃ (`descriptor_toGenerator_roundTrip` +
`descriptor_injective`), the function-form lookup pin
(`fxSignatureLookup_atTag`), and the three signature-value coherences
(`descriptor_tag_lt_generatorCount` + the two child-table consistencies).
Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The values -/

#assert_no_axioms FX1Poly.Core.Generator.descriptor
#assert_no_axioms FX1Poly.Core.GeneratorDescriptor.toGenerator
#assert_no_axioms FX1Poly.Core.fxSignatureLookup
#assert_no_axioms FX1Poly.Core.fxSignature

/-! ## The round-trip ≃ -/

#assert_no_axioms FX1Poly.Core.Generator.descriptor_toGenerator_roundTrip
#assert_no_axioms FX1Poly.Core.Generator.descriptor_injective
#assert_no_axioms FX1Poly.Core.fxSignatureLookup_atTag

/-! ## Signature-value coherence -/

#assert_no_axioms FX1Poly.Core.Generator.descriptor_tag_lt_generatorCount
#assert_no_axioms FX1Poly.Core.Generator.descriptor_childSpecsLength_eq_arity
#assert_no_axioms FX1Poly.Core.Generator.descriptor_scopeShifts_eq_binderShifts

end FX1PolyAudit
