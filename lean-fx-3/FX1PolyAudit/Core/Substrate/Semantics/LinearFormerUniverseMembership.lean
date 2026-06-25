import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Semantics.LinearFormerUniverseMembership

/-! # FX1PolyAudit.Core.Substrate.Semantics.LinearFormerUniverseMembership

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Substrate.Semantics.LinearFormerUniverseMembership`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Linear-logic type formers (linearArrow and tensorProduct) inhabit their universe too: both are two-child
-- .type formers, classified by dataFormerInUniverse on the two-child SN combinators (linearity is a usage
-- grade, orthogonal to the type-code-in-universe fact).
#assert_no_axioms FX1Poly.Core.linearArrow_isReducibleMemberOfUniverse

#assert_no_axioms FX1Poly.Core.tensorProduct_isReducibleMemberOfUniverse

end FX1PolyAudit
