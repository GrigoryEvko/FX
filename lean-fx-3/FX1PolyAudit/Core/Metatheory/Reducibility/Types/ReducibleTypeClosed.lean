import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeClosed

/-! # FX1PolyAudit.Core.Metatheory.Reducibility.Types.ReducibleTypeClosed

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeClosed`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Pointwise-saturation of the dependent reducibility relation (the level-free fundamental theorem's
-- choice-free piIntro keystone): `ReducibleTypeClosed` is closed under pointwise-iff by construction, so it
-- carries the canonical member-predicate candidate that bare `ReducibleType` does not.  Gated per-declaration
-- here, outside the AuditCoreSubstrate sweep's import closure.
#assert_no_axioms FX1Poly.Core.ReducibleTypeClosed

#assert_no_axioms FX1Poly.Core.ReducibleType.toClosed

#assert_no_axioms FX1Poly.Core.ReducibleType.closedAtMemberPredicate

end FX1PolyAudit
