import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Category.RawCategory

/-! # FX1PolyAudit.Polygraph.Category.RawCategory — zero-axiom gate (mirror shard)

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.Category.RawCategory`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`.  The generic raw-category
+ functor core: the identity functor, functor composition, and the unit /
associativity laws. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawFunctor.identity

#assert_no_axioms FX1Poly.Polygraph.RawFunctor.compose

#assert_no_axioms FX1Poly.Polygraph.RawFunctor.identity_compose

#assert_no_axioms FX1Poly.Polygraph.RawFunctor.compose_identity

#assert_no_axioms FX1Poly.Polygraph.RawFunctor.compose_assoc

end FX1PolyAudit
