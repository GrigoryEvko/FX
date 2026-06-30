import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.OmegacE.WordFreeMonoid

/-! # FX1PolyAudit.Polygraph.OmegacE.WordFreeMonoid

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.WordFreeMonoid`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- DIMENSION-1 FREE MONOID (one-object free category) on ωcE words — the Makkai word-problem arena.
-- Words under concatenation form a monoid (associativity + two-sided identity); suspension and the
-- word-code serialization are monoid homomorphisms.  The recursion base of Makkai's algorithm, the arena
-- the word equality modulo rewriting and the termination/confluence (= SN) of the FX presentation are
-- based at.  All proved propext-free (manual list inductions, not core List.append_assoc).
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.append_assoc

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.empty_append

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.append_empty

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.suspend_empty

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.suspend_append

#assert_no_axioms FX1Poly.OmegacE.OmegacEWordCode.append_assoc

#assert_no_axioms FX1Poly.OmegacE.OmegacEWordCode.empty_append

#assert_no_axioms FX1Poly.OmegacE.OmegacEWordCode.append_empty

#assert_no_axioms FX1Poly.OmegacE.OmegacEWordCode.ofWord_empty

#assert_no_axioms FX1Poly.OmegacE.OmegacEWordCode.toWord_empty

end FX1PolyAudit
