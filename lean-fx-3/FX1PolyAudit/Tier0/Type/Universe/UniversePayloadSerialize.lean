import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Type.Universe.UniversePayloadSerialize

/-! # FX1PolyAudit.Tier0.Type.Universe.UniversePayloadSerialize

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.Type.Universe.UniversePayloadSerialize`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.UniversePayload.encodeOnto

#assert_no_axioms FX1Poly.Universe.UniversePayload.encodePrefix

#assert_no_axioms FX1Poly.Universe.UniversePayload.decodeOnto

#assert_no_axioms FX1Poly.Universe.UniversePayload.decodeOnto_encodeOnto_reduce

#assert_no_axioms FX1Poly.Universe.UniversePayload.decodeOnto_encodeOnto

#assert_no_axioms FX1Poly.Universe.UniversePayload.decodeOnto_nodeCount_encodePrefix

end FX1PolyAudit
