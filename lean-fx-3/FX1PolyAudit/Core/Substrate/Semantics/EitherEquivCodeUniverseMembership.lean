import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Semantics.EitherEquivCodeUniverseMembership

/-! # FX1PolyAudit.Core.Substrate.Semantics.EitherEquivCodeUniverseMembership

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Substrate.Semantics.EitherEquivCodeUniverseMembership`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The two-child either/equiv codes complete the data-code family at the stratified layer, reusing the
-- two-child SN combinators (eitherCode/equivCode SN + Step.from_* inversions).  The whole universe-code-family
-- stratified membership (arrow/product/sum + list/option/either/id/equiv) is closed.
#assert_no_axioms FX1Poly.Core.eitherCode_isReducibleMemberOfUniverse

#assert_no_axioms FX1Poly.Core.equivCode_isReducibleMemberOfUniverse

end FX1PolyAudit
