import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Universe.UniverseFlagSerialize

/-! # FX1PolyAudit.Axis.Type.Universe.UniverseFlagSerialize

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Type.Universe.UniverseFlagSerialize`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.UniverseFlag.encodeOnto

#assert_no_axioms FX1Poly.Universe.UniverseFlag.encodePrefix

#assert_no_axioms FX1Poly.Universe.UniverseFlag.decode

#assert_no_axioms FX1Poly.Universe.UniverseFlag.decode_encodeOnto

#assert_no_axioms FX1Poly.Universe.UniverseFlag.decode_encodePrefix

end FX1PolyAudit
