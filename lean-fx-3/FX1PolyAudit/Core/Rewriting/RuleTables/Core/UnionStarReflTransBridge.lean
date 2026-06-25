import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Core.UnionStarReflTransBridge

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Core.UnionStarReflTransBridge

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Core.UnionStarReflTransBridge`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The snoc-vs-head closure bridge: the union's `UnionStar` (tailLeft/tailRight snoc form) and the generic
-- `ReflTransClosure` of the pointwise union (head form) coincide.  `UnionStar.head` prepends by recursion on
-- the fixed-start tail; the two transports are structural inductions.  This feeds `newmanGuarded` the union
-- reduction chains in its `ReflTransClosure` vocabulary (the `Acc (flip rel)` side already matches `UnionSuccessor`).
#assert_no_axioms FX1Poly.Core.UnionStar.head

#assert_no_axioms FX1Poly.Core.UnionStar.toReflTransClosure

#assert_no_axioms FX1Poly.Core.ReflTransClosure.toUnionStar

end FX1PolyAudit
