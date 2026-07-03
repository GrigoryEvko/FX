import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Category.Pullback

/-! # FX1PolyAudit.Polygraph.Category.Pullback — zero-axiom gate (mirror shard)

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.Category.Pullback`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`.  The generic limit core:
the strictness predicate, the leg-swap, and the pasting lemma (with their
strictness preservation). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.PullbackSquare.IsStrict

#assert_no_axioms FX1Poly.Polygraph.PullbackSquare.swap

#assert_no_axioms FX1Poly.Polygraph.PullbackSquare.swap_isStrict

#assert_no_axioms FX1Poly.Polygraph.PullbackSquare.paste

#assert_no_axioms FX1Poly.Polygraph.PullbackSquare.paste_isStrict

end FX1PolyAudit
