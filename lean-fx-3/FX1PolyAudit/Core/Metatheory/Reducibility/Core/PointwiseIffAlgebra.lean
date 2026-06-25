import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Reducibility.Core.PointwiseIffAlgebra

/-! # FX1PolyAudit.Core.Metatheory.Reducibility.Core.PointwiseIffAlgebra

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Reducibility.Core.PointwiseIffAlgebra`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Equivalence-relation algebra of candidate pointwise-iff (the transport algebra the reducibility model
-- threads through every `ReducibleType.deterministic` candidate transfer and the `ReducibleType.ofPointwiseIff`
-- congruence-closure cascade).
#assert_no_axioms FX1Poly.Core.PointwiseIff.refl

#assert_no_axioms FX1Poly.Core.PointwiseIff.symm

#assert_no_axioms FX1Poly.Core.PointwiseIff.trans

end FX1PolyAudit
