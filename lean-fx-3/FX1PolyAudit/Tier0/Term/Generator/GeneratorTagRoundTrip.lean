import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Generator.GeneratorTagRoundTrip

/-! # FX1PolyAudit.Tier0.Term.Generator.GeneratorTagRoundTrip

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.Term.Generator.GeneratorTagRoundTrip`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- §11.6.4 Generator-table validation: the FX0 prefix-code tag assignment
-- `Generator.toNat` is collision-free (injective), proved via the explicit left
-- inverse `Generator.fromTag` and its per-constructor round-trip.  The head byte
-- of the cell serialization therefore uniquely identifies the generator.
#assert_no_axioms FX1Poly.Core.Generator.fromTag

#assert_no_axioms FX1Poly.Core.Generator.fromTag_toNat

#assert_no_axioms FX1Poly.Core.Generator.toNat_injective

end FX1PolyAudit
