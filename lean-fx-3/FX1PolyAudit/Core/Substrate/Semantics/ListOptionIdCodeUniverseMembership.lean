import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Semantics.ListOptionIdCodeUniverseMembership

/-! # FX1PolyAudit.Core.Substrate.Semantics.ListOptionIdCodeUniverseMembership

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Substrate.Semantics.ListOptionIdCodeUniverseMembership`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Universe membership of the one/three-child data-type codes: list/option/id codes are reducible members of
-- Type@levelExpr, each a direct dataFormerInUniverse instance fed the per-former SN combinator + the uniform
-- weak-head-normal (only rootIota could unify, killed by cases iotaStep) + root-distinctness from
-- piTyCode/universeCode.
#assert_no_axioms FX1Poly.Core.listCode_isReducibleMemberOfUniverse

#assert_no_axioms FX1Poly.Core.optionCode_isReducibleMemberOfUniverse

#assert_no_axioms FX1Poly.Core.idCode_isReducibleMemberOfUniverse

end FX1PolyAudit
